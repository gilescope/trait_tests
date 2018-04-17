#![feature(proc_macro, )]//proc_macro_lib
#![crate_type = "proc-macro"]

extern crate proc_macro;
extern crate syn;
#[macro_use] extern crate quote;

//
// Example https://github.com/actix/actix-derive/blob/master/src/lib.rs
//

use proc_macro::{TokenStream};
use quote::__rt::TokenTree;
use syn::{TraitItem, TraitItemMethod,DeriveInput,  MethodSig, ItemTrait, Ident, FnDecl, ReturnType};

#[proc_macro_attribute]
pub fn trait_tests(_attr: TokenStream, input: TokenStream) -> TokenStream {
    // Construct a string representation of the type definition
    let output;
    if let Ok(trait_def) = syn::parse(input.clone()) {
        let mut ast: syn::ItemTrait = trait_def;
        ast = inject_test_all_method(ast);
        output= quote!(#ast);
    } else {
        panic!("Expected this attribute to be on a trait.");
    }
    //println!("trait_def: {:#?}", &output);
    output.into()
}

#[proc_macro_derive(TraitTests, attributes(trait_test))]
pub fn trait_tests2(input: TokenStream) -> TokenStream {
    // Parse the string representation
    let ast: DeriveInput  = syn::parse(input).unwrap();

    // Build the impl
    let gen = inject_test_method(ast);

    // Return the generated impl
    //println!("trait_derive: {:#?}", &gen);
    gen.into()
}

fn inject_test_method(_impl_def: DeriveInput) -> TokenStream {
    let mut results = quote::Tokens::new();

    for attr in _impl_def.attrs {
        results.append_all(process_case(_impl_def.ident, attr.tts));
    }

    results.into()
}

fn process_case(struct_ident: Ident, tts: quote::__rt::TokenStream) -> quote::Tokens {
    let mut it = tts.into_iter();
    let group = it.next();

    if let Some(TokenTree::Group(g @ quote::__rt::Group{..})) = group {
        let (trait_name, impltypes_y) = parse_case(g);
        let test_fn_name = generate_unique_test_name(&struct_ident, &trait_name, &impltypes_y);

        let has_generics_params = !impltypes_y.is_empty();
        let mut impltypes_punctuated = quote::Tokens::new();
        impltypes_punctuated.append_separated(impltypes_y, quote!(,));

        let new_fn : quote::Tokens = if !has_generics_params {
            quote!(
            #[test]
            fn #test_fn_name() {
                <#struct_ident as #trait_name>::test_all();
            }

            impl #trait_name for #struct_ident {})
        } else {
            quote!(
            #[test]
            fn #test_fn_name() {
                <#struct_ident<#impltypes_punctuated> as #trait_name>::test_all();
            }

            impl #trait_name for #struct_ident<#impltypes_punctuated> {})
        };
        new_fn
    } else { panic!("unexpected input") }
}

fn generate_unique_test_name(struct_ident: &Ident, trait_name: &quote::__rt::Term, params: &Vec<quote::Tokens>) -> Ident {
    let mut root = String::from(struct_ident.to_string());
    root.push('_');
    root.push_str(&trait_name.clone().to_string());
    for param in params {
        root.push('_');
        root.push_str(&param.clone().to_string());
    }
    let test_fn_name = syn::Ident::from(
        root.to_lowercase().replace("<", "_")
            .replace(">", "")
            .replace("\"", "")
            .replace(" ", "_")
            .replace("__", "_")
            .replace("__", "_")
    );
    test_fn_name
}

fn parse_case(g: quote::__rt::Group) -> (quote::__rt::Term, Vec<quote::Tokens>)
{
    let mut trait_name = None;
    let mut params : Vec<quote::Tokens> = vec![];
    let mut buffer : Vec<TokenTree> = vec![];
    for t in g.stream() {
        match t {
            TokenTree::Term(t) => {
                if trait_name.is_none() {
                    trait_name = Some(t.clone());
                } else {
                    buffer.push(TokenTree::Term(t));
                }
            },
            TokenTree::Op(op) if op.op() == ',' => {
                let mut parampp = quote::Tokens::new();
                parampp.append_all(buffer.clone());
                params.push(parampp);
                buffer.clear();
            },
            other @ _ => { buffer.push(other); }
        }
    }

    if params.len() > 0 {
        //That first param is created by the name of the trait test.
        params.remove(0);
    }
    if !buffer.is_empty() {
        let mut parampp = quote::Tokens::new();
        parampp.append_all(buffer);
        params.push(parampp);
    }
    (trait_name.unwrap(), params)
}

fn inject_test_all_method(trait_def: ItemTrait) -> ItemTrait {
    let mut items = trait_def.items.clone();
    let mut test_calls : Vec<Ident>= Vec::new();
    for item in items.iter() {
        if let &TraitItem::Method(TraitItemMethod{
                                      sig:MethodSig{
                                          ident:a,
                                          decl:FnDecl{output:ReturnType::Default, inputs:ref args, ..},
                                          ..},
                                      ..}) = item {
            if args.len() == 0 {
                test_calls.push(a);
            }
        }
    }

    let test_all_fn = syn::parse(quote!(
        fn test_all() {
            #(Self::#test_calls());*
        }
    ).into()).unwrap();

    items.push(test_all_fn);
    syn::ItemTrait{ items, ..trait_def }
}