//! `#[trait_tests]` defines a test suite on a trait; `#[test_impl]` runs it on an implementor.

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, TokenStreamExt};
use syn::punctuated::Punctuated;
use syn::token::Comma;
use syn::{
    AngleBracketedGenericArguments, AssocType, GenericArgument, Ident, Item, ItemImpl, ItemTrait,
    Path, PathArguments, PathSegment, ReturnType, Signature, TraitBound, TraitItem, TraitItemFn,
    Type, TypeParamBound, TypePath,
};

#[proc_macro_attribute]
pub fn trait_tests(_attr: TokenStream, input: TokenStream) -> TokenStream {
    //TODO: Error if test trait is not pub.
    let mut trait_def = match syn::parse(input) {
        Ok(Item::Trait(def)) => def,
        Ok(_) => panic!("This attribute must be used on a trait!"),
        Err(e) => panic!("Failed to parse input: {e}"),
    };

    let law_names = collect_law_names(&trait_def);
    trait_def = inject_test_all_method(trait_def, &law_names);
    let output = quote!(#trait_def);

    let mut tokens = proc_macro2::TokenStream::new();

    let trait_name_str = trait_def.ident.clone();

    // One `#[test]` per law. Exported at the crate root under the trait's own name
    // (separate namespace), so `use some_crate::XTests;` imports both trait and macro.
    let test_trait = trait_def.ident.clone();
    let law_fns = law_names.clone();
    let law_calls = law_names.clone();
    let test_trait_rep = vec![test_trait.clone(); law_names.len()];
    tokens.append_all(quote! {
        #[doc(hidden)]
        #[macro_export]
        macro_rules! #test_trait {
            ($t:ty) => {
                #( #[test] fn #law_fns() { <$t as #test_trait_rep>::#law_calls() } )*
            };
        }
    });

    let p: TypeParamBound = trait_def
        .supertraits
        .iter()
        .next()
        .expect("trait should have a supertrait that you are testing.")
        .clone();

    if let TypeParamBound::Trait(TraitBound { path, .. }) = p {
        let first_segment = path.segments.iter().next().unwrap();
        if let PathArguments::AngleBracketed(AngleBracketedGenericArguments { ref args, .. }) =
            first_segment.arguments
        {
            for (i, generic_arg) in args.iter().enumerate() {
                let gtype = match generic_arg {
                    GenericArgument::Type(gtype) => gtype,
                    GenericArgument::AssocType(AssocType { ty, .. }) => ty,
                    _ => continue,
                };
                let typename = Ident::new(
                    &format!("{}Type{}", trait_name_str, i + 1),
                    Span::call_site(),
                );
                tokens.append_all(quote!(#[allow(dead_code)] pub type #typename = #gtype;));
            }
        }

        //Add in type definitions...
        tokens.append_all(output);
        tokens.into()
    } else {
        panic!("Expected this attribute to be on a trait.");
    }
}

#[proc_macro_attribute]
pub fn test_impl(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let mut results = proc_macro2::TokenStream::new();
    let ast = match syn::parse(input) {
        Ok(Item::Impl(item)) => item,
        Ok(_) => panic!("Unexpected - needs to be on impl X for Y"),
        Err(e) => panic!("Failed to parse: {e}"),
    };

    results.append_all(quote!(#ast));

    let ItemImpl {
        trait_, self_ty, ..
    } = ast;
    let trait_ident = match trait_ {
        Some((_opt, ident, _for)) => ident,
        None => panic!("needs to be on an impl"),
    };
    let struct_type = match *self_ty {
        Type::Path(ref stype) => stype,
        _ => panic!("needs to be on an impl"),
    };

    let TypePath { path, .. } = struct_type.clone();
    let Path { segments, .. } = path;
    let seg1: PathSegment = segments[0].clone();
    let PathSegment { arguments, .. } = seg1;
    if let PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }) = arguments {
        let arg_uments: Vec<_> = args.iter().map(|_| quote!(a)).collect();
        results.append_all(process_case(struct_type, &trait_ident, &arg_uments));
    } else {
        results.append_all(process_case(struct_type, &trait_ident, &[]));
    }
    results.into()
}

fn process_case(
    struct_ident: &TypePath,
    trait_path: &Path,
    impltypes_y: &[proc_macro2::TokenStream],
) -> proc_macro2::TokenStream {
    let test_fn_name = generate_unique_test_name(struct_ident, trait_path, impltypes_y);

    let (trait_name, num_params_trait_takes) =
        get_type_with_filled_in_type_params_trait(trait_path);
    let trait_name_str = quote!(#trait_name).to_string();

    let TypePath { path, .. } = struct_ident;
    let impl_type_name =
        get_type_with_filled_in_type_params_impl(path, &trait_name_str, num_params_trait_takes);

    quote!( #[cfg(test)]
            mod #test_fn_name {
                #[allow(unused_imports)]
                use super::*;
                #trait_name!(#impl_type_name);
            }

            impl #trait_name for #impl_type_name {})
}

fn get_type_with_filled_in_type_params_trait(trait_path: &Path) -> (PathSegment, usize) {
    let Path { segments, .. } = trait_path;
    if segments.len() > 1 {
        panic!("untested");
    }
    let PathSegment { ident, arguments } = segments[0].clone();
    let arg_num = match arguments {
        PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }) => args.len(),
        PathArguments::None => 0,
        _ => panic!("unimplemented"),
    };
    (
        PathSegment {
            ident: Ident::new(&(quote!(#ident).to_string() + "Tests"), Span::call_site()),
            arguments: PathArguments::None,
        },
        arg_num,
    )
}

fn get_type_with_filled_in_type_params_impl(
    impl_path: &Path,
    trait_name: &str,
    num_params_trait_takes: usize,
) -> PathSegment {
    let Path { segments, .. } = impl_path;
    if segments.len() > 1 {
        panic!("untested");
    }
    let PathSegment { ident, arguments } = segments[0].clone();
    let ident = Ident::new(&quote!(#ident).to_string(), Span::call_site());
    let PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }) = arguments
    else {
        //Case no angle bracketed args on impl
        return PathSegment { ident, arguments };
    };

    //Impl has arguments.
    if num_params_trait_takes == args.len() {
        let final_args: PathArguments = if num_params_trait_takes == 0 {
            PathArguments::None
        } else {
            let names: Vec<String> = (1..=num_params_trait_takes)
                .map(|i| format!("{trait_name}Type{i}"))
                .collect();
            let ppf: AngleBracketedGenericArguments =
                syn::parse_str(&format!("<{}>", names.join(","))).unwrap();
            PathArguments::AngleBracketed(ppf)
        };
        PathSegment { ident, arguments: final_args }
    } else if num_params_trait_takes == 0 {
        //Case trait has no generic params, impl has generic params.
        //If these are non-concrete types we should substitute them.
        //For now we consider single letter 'T', 'U' etc. as being non-concrete types.
        let mut next_arg_num = 1;
        let mut concrete_args = Punctuated::<GenericArgument, Comma>::new();
        for arg in args {
            let arg_len = quote!(#arg).to_string().len();
            if arg_len < 2 {
                let new_arg = format!("{}Type{}", trait_name, next_arg_num);
                let ga: GenericArgument = syn::parse_str(&new_arg).unwrap();
                concrete_args.push(ga);
                next_arg_num += 1;
            } else {
                concrete_args.push(arg);
            }
        }
        PathSegment {
            ident,
            arguments: PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                colon2_token: None,
                lt_token: Default::default(),
                args: concrete_args,
                gt_token: Default::default(),
            }),
        }
    } else {
        panic!("consider case");
    }
}

fn generate_unique_test_name(
    struct_ident: &TypePath,
    trait_name: &Path,
    params: &[proc_macro2::TokenStream],
) -> Ident {
    let mut root = quote!(#struct_ident).to_string();
    root.push('_');
    root.push_str(&quote!(#trait_name).to_string());
    for param in params {
        root.push('_');
        root.push_str(&param.to_string());
    }
    Ident::new(
        &root
            .to_lowercase()
            .replace('<', "_")
            .replace(['>', '"'], "")
            .replace([' ', ','], "_")
            .replace("__", "_")
            .replace("__", "_"),
        Span::call_site(),
    )
}

/// Creates a method that runs all the test methods that this trait defines.
/// Takes in a trait item and outputs that same item with the added method.
fn inject_test_all_method(mut trait_def: ItemTrait, test_calls: &[Ident]) -> ItemTrait {
    let test_all_fn = syn::parse(
        quote!(
            fn test_all() {
                #(Self::#test_calls());*
            }
        )
        .into(),
    )
    .unwrap();

    trait_def.items.push(test_all_fn);
    trait_def
}

/// A law is a trait method with no arguments and no return type.
fn collect_law_names(trait_def: &ItemTrait) -> Vec<Ident> {
    trait_def
        .items
        .iter()
        .filter_map(|item| match item {
            TraitItem::Fn(TraitItemFn {
                sig: Signature { ident, inputs, output: ReturnType::Default, .. },
                ..
            }) if inputs.is_empty() => Some(ident.clone()),
            _ => None,
        })
        .collect()
}
