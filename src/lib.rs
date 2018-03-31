#![crate_type = "dylib"]
#![feature(plugin_registrar, rustc_private, quote)]

extern crate syntax;
extern crate rustc_plugin;

use syntax::abi::Abi;
use syntax::ast::{self, Ident, Generics, Item, TraitItemKind, TraitRef, TraitItem, Path,
                  WhereClause, PathParameters, Ty, AngleBracketedParameterData,
                  PathSegment, ExprKind,Expr, ItemKind, StmtKind, Stmt, TyKind, MethodSig,
                  Unsafety, Constness, FunctionRetTy, FnDecl };
use syntax::codemap::{ self, Spanned};
use syntax::ext::base::{ExtCtxt, MultiModifier, Annotatable};
use syntax::ext::build::AstBuilder;
use syntax::ptr::P;
use syntax::symbol::Symbol;
use syntax::tokenstream::{TokenStream};
use syntax::util::ThinVec;

use rustc_plugin::Registry;

//
// leftfield: could trait annotation create a macro that would create the individual test functions
// when invoked with a param at the impl site?
//
#[plugin_registrar]
#[doc(hidden)]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_syntax_extension(Symbol::intern("trait_tests"),
                                  MultiModifier(Box::new(expand_meta_trait_test)));
}

fn expand_meta_trait_test(cx: &mut ExtCtxt,
                          span: codemap::Span,
                          _: &ast::MetaItem,
                          annot_item: Annotatable) -> Vec<Annotatable> {
    let item_kind;
    let item = annot_item.expect_item();
    {
        match item.node {
            ItemKind::Impl(_, _, _, _, Some(TraitRef { path: ref trait_ref, .. } ), ref impl_type, _) => {
                // ![trait_tests] has been put on an implementation,
                // we need to generate a test that calls the test_all() function defined on the trait.
                // We look like:
                //
                // impl SetTestsisize for MySet<isize> {}
                //                                ^---- unangled is set to this type.
                match trait_ref { &Path{ ref segments, .. } => {
                        let trait_segments = segments;
                        let trait_ident = trait_segments[0].identifier.clone();
                        let trait_name = trait_ident.name.to_string();

                        match **impl_type {
                            Ty {
                                id: ast::DUMMY_NODE_ID,
                                node: TyKind::Path(None, Path{ segments: ref a, .. }),
                                ..
                            } => {
                                match a[0] {
                                    PathSegment { parameters: ref maybe_angle, identifier: ref type_impl_ident, .. } => {
                                        let mut _unangled: Option<Ty> = None;

                                        if let &Some(ref angle) = maybe_angle {
                                            if let PathParameters::AngleBracketed(
                                                AngleBracketedParameterData { types: ref _unangled, .. }) = **angle {
                                                //Sideeffect! sets 'unangled' to the impl type's generic parameter.
                                            }
                                        }

                                        let type_impl_name = &type_impl_ident.name.to_string().clone();

                                        let trate_ref_clone = trait_ref.clone();
                                        let impl_type_clone = impl_type.clone();

                                        let test_all_call = quote_stmt!(&mut *cx, <$impl_type_clone as $trate_ref_clone>::test_all();).unwrap();

                                        let body = cx.block(span, vec![test_all_call]);

                                        let test_method_name = String::from("trait_test_")
                                            + &type_impl_name.to_lowercase() +
                                            "_" + &trait_name.to_lowercase();

                                        let test = cx.item_fn(span, Ident::from_str(&test_method_name),
                                                              vec![], cx.ty(span, TyKind::Tup(vec![])), body);

                                        // Copy attributes from original function
                                        let mut attrs = item.attrs.clone();

                                        // Add #[test] attribute
                                        attrs.push(cx.attribute(span, cx.meta_word(span, Symbol::intern("test"))));

                                        // Attach the attributes to the outer function
                                        let test_fn = Annotatable::Item(P(ast::Item {attrs, ..(*test).clone()}));

                                        return  vec![Annotatable::Item(P(Item{attrs: Vec::new(), ..(*item).clone() })), test_fn];
                                    }
                                }
                            },
                            _ => {}
                        }
                    }
                }
            },
            ItemKind::Trait(a, b, ref c, ref d, ref trait_items) => {
                // ![trait_tests] has been put on a trait, we need to generate a test_all() function.
                let mut test_names = vec![];

                for method in trait_items {
                    match method {
                        &TraitItem {
                            generics:Generics{ params: ref v, ..},
                            node:TraitItemKind::Method(
                                MethodSig{ decl: ref fn_decl, .. }, Some(_)),
                            ..
                        } if v.is_empty() => {
                            match **fn_decl {
                                FnDecl{inputs: ref args, ..} if args.is_empty() => {
                                    let fn_call = Stmt {
                                        id: ast::DUMMY_NODE_ID,
                                        node: StmtKind::Semi(P(Expr {
                                            id: ast::DUMMY_NODE_ID,
                                            node: ExprKind::Call(P(Expr {
                                                span,
                                                attrs: ThinVec::new(),
                                                id: ast::DUMMY_NODE_ID,
                                                node:
                                                ExprKind::Path(None, ::syntax::ast::Path {
                                                    span,
                                                    segments: vec![
                                                        PathSegment { span, parameters: None, identifier: Ident::from_str("Self") },
                                                        PathSegment { span, parameters: None, identifier: method.ident.clone() },
                                                    ]
                                                })
                                            }), vec![]),
                                            span,
                                            attrs: ThinVec::new()
                                        })),
                                        span,
                                    };
                                    test_names.push(fn_call);
                                },
                                _ => {}
                            }
                        },
                        _ => {}
                    }
                }

                let body = cx.block(span, test_names);

                let func = ::syntax::ast::TraitItemKind::Method(MethodSig {
                        abi: Abi::Rust,
                        constness: Spanned {
                            node: Constness::NotConst,
                            span
                        },
                        decl: P(FnDecl {
                            inputs: vec![],
                            output: FunctionRetTy::Default(
                                span
                            ),
                            variadic: false
                        }),

                        unsafety: Unsafety::Normal
                    }, Some(body) );

                let prop = ast::TraitItem {
                    attrs: Vec::new(),
                    ident: Ident::from_str("test_all"),
                    tokens: Some(TokenStream::empty()),
                    id:ast::DUMMY_NODE_ID,
                    span,
                    generics: Generics{span, where_clause:WhereClause{
                        id:ast::DUMMY_NODE_ID,
                        span,
                        predicates:vec![]}, params:vec![]},
                    node: func
                };

                let mut items = trait_items.clone();
                items.push(prop);
                item_kind = ItemKind::Trait(a, b, c.clone(), d.clone(), items);
                return vec![Annotatable::Item(P(Item{ node: item_kind, ..(*item).clone() }))]
            }
            _ => {
                cx.span_err(
                    span, "#[trait_tests] only supported on traits and associated impls");
            }
        }
    }
    vec![Annotatable::Item(P(Item{  ..(*item).clone() }))]
}