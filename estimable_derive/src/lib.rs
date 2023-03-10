extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{format_ident, quote};

#[proc_macro_derive(FixedLength)]
pub fn fixedlength_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();

    impl_fixedlength(&ast)
}

fn impl_fixedlength(ast: &syn::DeriveInput) -> TokenStream {
    let fixed_len_trait = quote! { tedium::conv::len::FixedLength };

    let name = &ast.ident;
    let gen = match &ast.data {
        syn::Data::Enum(_) => unimplemented!(),
        syn::Data::Union(_) => unimplemented!(),
        syn::Data::Struct(syn::DataStruct { fields, .. }) => match fields {
            syn::Fields::Unit => {
                quote! {
                    impl #fixed_len_trait for #name {
                        const LEN : usize = 0;
                    }
                }
            }
            syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, .. }) => match unnamed.len() {
                0 => {
                    quote! {
                        impl #fixed_len_trait for #name {
                            const LEN : usize = 0;
                        }
                    }
                }
                _ => {
                    let ty = unnamed.iter().map(|x| &x.ty);
                    quote! {
                    impl #fixed_len_trait for #name {
                        const LEN : usize =
                            #( <#ty as #fixed_len_trait>::LEN )+*
                        };
                    }
                }
            },
            syn::Fields::Named(syn::FieldsNamed { named, .. }) => match named.len() {
                0 => {
                    quote! {
                        impl #fixed_len_trait for #name {
                            const LEN : usize = 0;
                        }
                    }
                }
                _ => {
                    let ty = named.iter().map(|x| &x.ty);
                    quote! {
                        impl #fixed_len_trait for #name {
                            const LEN : usize = #( <#ty as #fixed_len_trait>::LEN )+*;
                        }
                    }
                }
            },
        },
    };
    gen.into()
}

#[proc_macro_derive(Estimable)]
pub fn estimable_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();

    impl_estimable(&ast)
}

fn impl_estimable(ast: &syn::DeriveInput) -> TokenStream {
    let fixed_len_trait = quote! { tedium::conv::len::FixedLength };
    let estimable_trait = quote! { tedium::conv::len::Estimable };
    let some = quote! { ::std::option::Option::Some };
    let none = quote! { ::std::option::Option::None };

    let name = &ast.ident;
    let gen = match &ast.data {
        syn::Data::Enum(_) => unimplemented!(),
        syn::Data::Union(_) => unimplemented!(),
        syn::Data::Struct(syn::DataStruct { fields, .. }) => match fields {
            syn::Fields::Unit => {
                quote! {
                    impl #fixed_len_trait for #name {
                        const LEN : usize = 0;
                    }
                }
            }
            syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed, .. }) => match unnamed.len() {
                0 => {
                    quote! {
                        impl #fixed_len_trait for #name {
                            const LEN : usize = 0;
                        }
                    }
                }
                1 => {
                    let syn::Field { ty, .. } = unnamed.first().unwrap();
                    quote! {
                        impl #estimable_trait for #name {
                            const KNOWN : Option<usize> = <#ty as #estimable_trait>::KNOWN;

                            fn unknown(&self) -> usize {
                                <#ty as #estimable_trait>::unknown(&self.0)
                            }
                        }
                    }
                }
                _ => {
                    let i = (0..unnamed.len()).map(syn::Index::from);
                    let varname: Vec<syn::Ident> = (0..unnamed.len())
                        .map(|x| format_ident!("pos{}", x))
                        .collect();
                    let ty = unnamed.iter().map(|x| &x.ty);
                    quote! {
                        impl #estimable_trait for #name {
                            const KNOWN : Option<usize> = {
                                const fn f( #( #varname : Option<usize> ),* ) -> Option<usize> {
                                    match ( #( #varname ),* ) {
                                        ( #( #some(#varname) ),* ) => ( #some(#(#varname)+*)),
                                        _ => #none,
                                    }
                                }
                                f( #( <#ty as #estimable_trait>::KNOWN ),* )
                            };

                            fn unknown(&self) -> usize {
                                #[cfg(not(Estimable))] use #estimable_trait;

                                #( self.#i.unknown() )+*
                            }
                        }
                    }
                }
            },
            syn::Fields::Named(syn::FieldsNamed { named, .. }) => match named.len() {
                0 => {
                    quote! {
                        impl #fixed_len_trait for #name {
                            const LEN : usize = 0;
                        }
                    }
                }
                _ => {
                    let (fname, ty): (Vec<&syn::Ident>, Vec<&syn::Type>) = named
                        .iter()
                        .map(|x| (x.ident.as_ref().unwrap(), &x.ty))
                        .unzip();
                    quote! {
                        impl #estimable_trait for #name {
                            const KNOWN : Option<usize> = {
                                const fn f( #( #fname : Option<usize> ),* ) -> Option<usize> {
                                    match ( #( #fname ),* ) {
                                        ( #( #some(#fname)),* ) => #some( #(#fname)+* ),
                                        _ => #none,
                                    }
                                }
                                f( #( <#ty as #estimable_trait>::KNOWN ),* )
                            };

                            fn unknown(&self) -> usize {
                                #[cfg(not(Estimable))] use #estimable_trait;

                                #( self.#fname.unknown() )+*
                            }
                        }
                    }
                }
            },
        },
    };
    gen.into()
}
