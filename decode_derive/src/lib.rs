extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;

#[proc_macro_derive(Decode)]
pub fn decode_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();

    impl_decode(&ast)
}

fn impl_decode(ast: &syn::DeriveInput) -> TokenStream {
    let decode_trait = quote! { tedium::conv::Decode };
    let parser_trait = quote! { tedium::parse::Parser };
    let parse_result_type = quote! { tedium::parse::ParseResult };


    let name = &ast.ident;
    let gen = match &ast.data {
        syn::Data::Enum(_) => unimplemented!("Derive macro `Decode` not implemented for enums"),
        syn::Data::Union(_) => unimplemented!("Derive macro `Decode` not implemented for unions"),
        syn::Data::Struct(syn::DataStruct { fields, .. }) => match fields {
            syn::Fields::Unit => {
                quote! {
                    impl #decode_trait for #name {
                        fn parse<P: #parser_trait>(_: &mut P) -> #parse_result_type<Self> {
                            Ok(Self)
                        }
                    }
                }
            }
            syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, .. }) => {
                let ty = unnamed.iter().map(|x| &x.ty);
                quote! {
                    impl #decode_trait for #name {
                        fn parse<P: #parser_trait>(p: &mut P) -> #parse_result_type<Self> {
                            Ok(Self(#( <#ty as #decode_trait>::parse(p)? ),*))
                        }
                    }
                }
            }
            syn::Fields::Named(syn::FieldsNamed { named, .. }) => {
                let (fname, ty): (Vec<&syn::Ident>, Vec<&syn::Type>) = named
                    .iter()
                    .map(|x| (x.ident.as_ref().unwrap(), &x.ty))
                    .unzip();
                quote! {
                    impl #decode_trait for #name {
                        fn parse<P: #parser_trait>(p: &mut P) -> #parse_result_type<Self> {
                            Ok(Self { #( #fname: <#ty as #decode_trait>::parse(p)? ),* })
                        }
                    }
                }
            }
        },
    };
    gen.into()
}
