extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn;

#[proc_macro_derive(Encode)]
pub fn encode_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();

    impl_encode(&ast)
}

fn impl_encode(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let gen = match &ast.data {
        syn::Data::Enum(_) => unimplemented!(),
        syn::Data::Union(_) => unimplemented!(),
        syn::Data::Struct(syn::DataStruct { fields, .. }) => match fields {
            syn::Fields::Unit => {
                quote! {
                    impl Encode for #name {
                        fn write(&self, _: &mut Vec<u8>) {}
                    }
                }
            },
            syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, ..}) => {
                let i = (0..unnamed.len()).map(syn::Index::from);
                quote! {
                    impl Encode for #name {
                        fn write(&self, buf: &mut Vec<u8>) {
                            #( self.#i.write(buf); )*
                        }
                    }
                }
            },
            syn::Fields::Named(syn::FieldsNamed { named, .. }) => {
                let ident = named.iter().map(|field| field.ident.as_ref().unwrap());
                quote! {
                    impl Encode for #name {
                        fn write(&self, buf: &mut Vec<u8>) {
                            #( self.#ident.write(buf); )*
                        }
                    }
                }
            }
        },
    };
    gen.into()
}
