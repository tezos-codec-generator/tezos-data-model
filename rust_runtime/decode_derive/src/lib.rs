extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn;

#[proc_macro_derive(Decode)]
pub fn decode_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();

    impl_decode(&ast)
}

fn impl_decode(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let gen = match &ast.data {
        syn::Data::Enum(_) => unimplemented!(),
        syn::Data::Union(_) => unimplemented!(),
        syn::Data::Struct(syn::DataStruct { fields, .. }) => match fields {
            syn::Fields::Unit => {
                quote! {
                    impl Decode for #name {
                        fn parse<P: Parser>(_: &mut P) -> ParseResult<Self> {
                            Ok(Self())
                        }
                    }
                }
            },
            syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, ..}) => {
                let ty = unnamed.iter().map(|x| &x.ty);
                quote! {
                    impl Decode for #name {
                        fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
                            Ok(Self(#( <#ty as Decode>::parse(p)? ),*))
                        }
                    }
                }
            },
            syn::Fields::Named(syn::FieldsNamed { named, ..}) => {
                let (fname, ty) : (Vec<&syn::Ident>, Vec<&syn::Type>) = named.iter().map(|x| (x.ident.as_ref().unwrap(), &x.ty)).unzip();
                quote! {
                    impl Decode for #name {
                        fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
                            Ok(Self { #( #fname: <#ty as Decode>::parse(p)? ),* })
                        }
                    }
                }
            }
        },
    };
    gen.into()
}
