#![crate_type = "dylib"]
#![feature(plugin_registrar, rustc_private)]

extern crate syntax;
extern crate rustc_plugin;

use syntax::abi::Abi;
use syntax::ast::{self, Ident, Generics, Item, TraitItemKind, AngleBracketed, TraitRef, TraitItem, Path,
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
            ItemKind::Impl(_, _, _, _, Some(TraitRef { path: ref trait_ref, ref_id:_} ),
                            ref impl_type, _) => {
                // ![trait_tests] has been put on an implementation,
                // we need to generate a test that calls the test_all() function defined on the trait.
                //We look like: impl SetTestsisize for MySet<isize> {}

                //let ty = impl_type.clone();
                let mut unangled : Option<Ty> = None;

                match **impl_type {
                    Ty{
                        id: ast::DUMMY_NODE_ID,
                        node : TyKind::Path(None,
                                            Path{
                                                segments: ref a, ..}
                        ),
                        ..} => {

                        match a[0] {
                            PathSegment{
                                parameters: Some(
                                    ref angle

                                ),
                                ..
                            } => {

                                if let AngleBracketed(AngleBracketedParameterData{types: ref unangled, .. }) = **angle
                                {
                                    println!("matched {:#?}", &unangled)
                                }
                            }
                            _ => {}
                        }


//                        println!("matched {:#?}", a)
                    },
                    _ => {}
                }


                let s : String = format!("{:?}",impl_type);
                //let mut type_param = None;
               // let mut unangled = None;
                let type_impl_name : &str = if let Some(idx) = s.find('<') { // TODO dodgy
                    //let type_param = Some(&s[idx .. s.len() - 1]);
                //    unangled = Some(&(type_param.unwrap()[1 .. type_param.unwrap().len()-1]));//TODO dodgy
                    &s[5..idx]
                } else {
                    &s[5..s.len() - 1]
                };

                let trait_name = format!("{:?}", trait_ref); // TODO dodgy
                let trait_name_lower = trait_name[5..trait_name.len()-1].to_lowercase();

                let angles = if let Some(angle_ty) = unangled {
//                    let mut type_param_path = vec![ ];
//                    type_param_path.push(PathSegment{ span, parameters: None, identifier: Ident::from_str(x) });

                    Some(P(PathParameters::AngleBracketed(AngleBracketedParameterData {
                        span,
                        lifetimes: vec![],
                        bindings: vec![],
                        types: vec![P(

                        angle_ty.clone()
//                            Ty {
//                            id: ast::DUMMY_NODE_ID,
//                            node: TyKind::Path(None, Path { segments: type_param_path, span }),//tODO!!
//                            span
//                        }

                        )]
                    })))
                } else {
                    None
                };

                let test_all_call = Stmt {
                    id: ast::DUMMY_NODE_ID,
                    node: StmtKind::Expr(P(Expr{
                        span,
                        attrs: ThinVec::new(),
                        id: ast::DUMMY_NODE_ID,
                        node: ExprKind::Call(P(Expr {
                            span,
                            attrs: ThinVec::new(),
                            id: ast::DUMMY_NODE_ID,
                            node:
                            ExprKind::Path(None, ::syntax::ast::Path {
                                span,
                                segments: vec![
                                    PathSegment { span, parameters: angles, identifier: Ident::from_str(type_impl_name) },//TODO dodgy
                                    PathSegment { span, parameters: None, identifier: Ident::from_str("test_all") },
                                ]
                            }
                            )
                        }), vec![])
                    })),
                    span,
                };

                let body = cx.block(span, vec![test_all_call]);

                let test = cx.item_fn(span, Ident::from_str(&(String::from("trait_test_")
                    + &type_impl_name.to_lowercase() +
                    "_" + &trait_name_lower )), vec![], cx.ty(span, TyKind::Tup(vec![])), body);

                // Copy attributes from original function
                let mut attrs = item.attrs.clone();

                // Add #[test] attribute
                attrs.push(cx.attribute(span, cx.meta_word(span, Symbol::intern("test"))));

                // Attach the attributes to the outer function
                let test_fn = Annotatable::Item(P(ast::Item {attrs, ..(*test).clone()}));

                return  vec![Annotatable::Item(P(Item{attrs: Vec::new(), ..(*item).clone() })), test_fn];
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