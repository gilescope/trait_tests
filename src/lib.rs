extern crate proc_macro;
extern crate proc_macro2;
extern crate syn;
#[macro_use]
extern crate quote;

//
// Example https://github.com/actix/actix-derive/blob/master/src/lib.rs
//

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::TokenStreamExt;
use syn::token::Comma;
use syn::{
    AngleBracketedGenericArguments, Binding, FnDecl, GenericArgument, Ident, Item, ItemImpl,
    ItemTrait, MethodSig, Path, PathArguments, PathSegment, ReturnType, TraitBound, TraitItem,
    TraitItemMethod, Type, TypeParamBound, TypePath,
};

#[cfg_attr(feature = "cargo-clippy", allow(needless_pass_by_value))]
#[proc_macro_attribute]
pub fn trait_tests(_attr: TokenStream, input: TokenStream) -> TokenStream {
    // Construct a string representation of the type definition

    //TODO: Error if test trait is not pub.
    let mut trait_def = match syn::parse(input) {
        Ok(Item::Trait(def)) => def,
        Ok(_) => panic!("This attribute must be used on a trait!"),
        Err(_) => panic!("Failed to parse input"),
    };

    trait_def = inject_test_all_method(trait_def);
    let output = quote!(#trait_def); //TODO loses span information!

    let mut tokens = proc_macro2::TokenStream::new();

    let trait_name_str = trait_def.ident.clone();

    let p: TypeParamBound = trait_def
        .supertraits
        .iter()
        .nth(0)
        .expect("trait should have a supertrait that you are testing.")
        .clone();

    if let TypeParamBound::Trait(TraitBound { path, .. }) = p {
        let first_segment = path.segments.iter().nth(0).unwrap();
        if let PathArguments::AngleBracketed(AngleBracketedGenericArguments { ref args, .. }) =
            first_segment.arguments
        {
            for (i, generic_arg) in args.iter().enumerate() {
                match generic_arg {
                    GenericArgument::Type(gtype) => {
                        let typename = Ident::new(
                            &format!("{}Type{}", trait_name_str, i + 1),
                            Span::call_site(),
                        );
                        tokens.append_all(quote!(#[allow(dead_code)] pub type #typename = #gtype;));
                    }
                    GenericArgument::Binding(Binding {
                        ty: gtype,
                        ident: _ident,
                        ..
                    }) => {
                        let typename = Ident::new(
                            &format!("{}Type{}", trait_name_str, i + 1),
                            Span::call_site(),
                        );
                        tokens.append_all(quote!(#[allow(dead_code)] pub type #typename = #gtype;));
                    }
                    _ => { /* ignore */ }
                }
            }
        }

        //Add in type definitions...
        tokens.append_all(output);
        //println!("trait_def: {:#?}", &tokens);
        return tokens.into();
    } else {
        panic!("Expected this attribute to be on a trait.");
    }
}

#[cfg_attr(feature = "cargo-clippy", allow(needless_pass_by_value))]
#[proc_macro_attribute]
pub fn test_impl(_attr: TokenStream, input: TokenStream) -> TokenStream {
    let mut results = proc_macro2::TokenStream::new();
    let ast = match syn::parse(input) {
        Ok(Item::Impl(item)) => item,
        Ok(_) => panic!("Unexpected - needs to be on impl X for Y"),
        Err(_) => panic!("Failed to parse!"),
    };

    results.append_all(quote!(#ast)); //TODO loses span information!

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
        let mut arg_uments = vec![];
        for _arg in args.iter() {
            arg_uments.push(quote!(a));
        }

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
    let test_fn_name = generate_unique_test_name(struct_ident, trait_path, &impltypes_y);

    let mut impltypes_punctuated = proc_macro2::TokenStream::new();
    let (trait_name, num_params_trait_takes) =
        get_type_with_filled_in_type_params_trait(trait_path);
    let trait_name_str = quote!(#trait_name).to_string();

    let mut v = vec![];
    for (i, _) in impltypes_y.iter().enumerate() {
        v.push(Ident::new(
            &format!("{}Type{}", trait_name_str, i),
            Span::call_site(),
        ))
    }

    impltypes_punctuated.append_separated(v, quote!(,));

    let TypePath { path, .. } = struct_ident;
    let impl_type_name =
        get_type_with_filled_in_type_params_impl(path, &trait_name_str, num_params_trait_takes);

    quote!( #[test]
            fn #test_fn_name() {
                <#impl_type_name as #trait_name>::test_all();
            }

            impl #trait_name for #impl_type_name {})
}

fn get_type_with_filled_in_type_params_trait(trait_path: &Path) -> (PathSegment, usize) {
    let Path { segments, .. } = trait_path;
    if segments.len() > 1 {
        panic!("untested");
    } else {
        let PathSegment { ident, arguments } = segments[0].clone();
        let arg_num = match arguments {
            PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }) => {
                args.len()
            }
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
}

fn get_type_with_filled_in_type_params_impl(
    impl_path: &Path,
    trait_name: &str,
    num_params_trait_takes: usize,
) -> PathSegment {
    let Path { segments, .. } = impl_path;
    if segments.len() > 1 {
        panic!("untested");
    } else {
        let PathSegment { ident, arguments } = segments[0].clone();
        if let PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }) =
            arguments
        {
            //Impl has arguments.
            if num_params_trait_takes == args.len() {
                let mut s = String::from("<");
                for arg in 0..num_params_trait_takes {
                    if arg > 0 {
                        s.push(',');
                    }
                    s.push_str(&format!("{}Type{}", trait_name, arg + 1));
                }
                s.push('>');
                let final_args: PathArguments = if num_params_trait_takes == 0 {
                    PathArguments::None
                } else {
                    let ppf: AngleBracketedGenericArguments = syn::parse_str(&s).unwrap();
                    PathArguments::AngleBracketed(ppf)
                };
                PathSegment {
                    ident: Ident::new(&(quote!(#ident).to_string()), Span::call_site()),
                    arguments: final_args,
                }
            } else if num_params_trait_takes == 0 {
                //Case trait has no generic params, impl has generic params.
                //If these are non-concrete types we should substitute them.
                //For now we consider single letter 'T', 'U' etc. as being non-concrete types.
                let mut next_arg_num = 1;
                let mut concrete_args =
                    syn::punctuated::Punctuated::<GenericArgument, Comma>::new();
                for arg in args {
                    let arg_len = quote!(#arg).to_string().len();
                    if arg_len < 2 {
                        let new_arg = format!("{}Type{}", trait_name, next_arg_num);
                        let ga: GenericArgument = syn::parse_str(&new_arg).unwrap();
                        concrete_args.push_value(ga);
                        next_arg_num += 1;
                    } else {
                        concrete_args.push_value(arg);
                    }
                }

                //leave well alone - keep the arguments as these are likely to be concrete types rather than bindings...:

                PathSegment {
                    ident: Ident::new(&(quote!(#ident).to_string()), Span::call_site()),
                    arguments: PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                        colon2_token: None,
                        lt_token: syn::token::Lt([Span::call_site()]),
                        args: concrete_args,
                        gt_token: syn::token::Gt([Span::call_site()]),
                    }),
                }
            } else {
                panic!("consider case");
            }
        } else {
            //Case no angle bracketed args on impl
            PathSegment {
                ident: Ident::new(&(quote!(#ident).to_string()), Span::call_site()),
                arguments,
            }
        }
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
        root.push_str(&param.clone().to_string());
    }
    syn::Ident::new(
        &root
            .to_lowercase()
            .replace("<", "_")
            .replace(">", "")
            .replace("\"", "")
            .replace(" ", "_")
            .replace(",", "_")
            .replace("__", "_")
            .replace("__", "_"),
        Span::call_site(),
    )
}

/// Creates a method that runs all the test methods that this trait defines.
/// Takes in a trait item and outputs that same item with the added method.
fn inject_test_all_method(mut trait_def: ItemTrait) -> ItemTrait {
    // A list of functions that will end up being run on test
    let mut test_calls: Vec<Ident> = Vec::with_capacity(trait_def.items.len());
    for item in &trait_def.items {
        // Tests don't return anything...
        if let TraitItem::Method(TraitItemMethod {
            sig:
                MethodSig {
                    ident: ref call_signature,
                    decl:
                        FnDecl {
                            output: ReturnType::Default,
                            inputs: ref args,
                            ..
                        },
                    ..
                },
            ..
        }) = item
        {
            // ... and don't take any arguments either
            if args.is_empty() {
                test_calls.push(call_signature.clone());
            }
        }
    }

    // The function that contains all the tests
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
