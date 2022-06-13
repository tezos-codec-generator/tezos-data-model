extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;

#[proc_macro_derive(Encode)]
pub fn encode_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();

    impl_encode(&ast)
}

fn impl_encode(ast: &syn::DeriveInput) -> TokenStream {
    let encode_trait = quote! { rust_runtime::conv::Encode };
    let target_trait = quote! { rust_runtime::conv::target::Target };
    let resolve_zero_fn = quote! { rust_runtime::resolve_zero! };

    let name = &ast.ident;
    let gen = match &ast.data {
        syn::Data::Enum(_) => unimplemented!(),
        syn::Data::Union(_) => unimplemented!(),
        syn::Data::Struct(syn::DataStruct { fields, .. }) => match fields {
            syn::Fields::Unit => {
                quote! {
                    impl #encode_trait for #name {
                        fn write_to<U: #target_trait>(&self, buf: &mut U) -> usize {
                            #resolve_zero_fn(buf)
                        }
                    }
                }
            },
            syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, ..}) => {
                let i = (0..unnamed.len()).map(syn::Index::from);
                quote! {
                    impl #encode_trait for #name {
                        fn write_to<U: #target_trait>(&self, buf: &mut U) -> usize {
                            #[cfg(not(Encode))] use #encode_trait;

                            #( self.#i.write_to(buf) + )* #resolve_zero_fn(buf)
                        }
                    }
                }
            },
            syn::Fields::Named(syn::FieldsNamed { named, .. }) => {
                let ident = named.iter().map(|field| field.ident.as_ref().unwrap());
                quote! {

                    impl #encode_trait for #name {
                        fn write_to<U: #target_trait>(&self, buf: &mut U) -> usize {
                            #[cfg(not(Encode))] use #encode_trait;

                            #( self.#ident.write_to(buf) + )* #resolve_zero_fn(buf)
                        }
                    }
                }
            }
        },
    };
    gen.into()
}
