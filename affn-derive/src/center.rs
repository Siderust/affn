use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{DeriveInput, Expr, Lit, Meta, Type};

pub(crate) struct CenterAttributes {
    pub name: Option<String>,
    pub params: Option<Type>,
    pub affine: bool,
}

impl Default for CenterAttributes {
    fn default() -> Self {
        Self {
            name: None,
            params: None,
            affine: true,
        }
    }
}

pub(crate) fn derive_reference_center_impl(input: DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;

    let attrs = parse_center_attributes(&input)?;

    let name_expr = match attrs.name {
        Some(custom_name) => quote! { #custom_name },
        None => {
            let name_str = name.to_string();
            quote! { #name_str }
        }
    };

    let params_type = match attrs.params {
        Some(ty) => quote! { #ty },
        None => quote! { () },
    };

    let affine_impl = if attrs.affine {
        quote! {
            impl ::affn::centers::AffineCenter for #name {}
        }
    } else {
        quote! {}
    };

    let expanded = quote! {
        impl ::affn::centers::ReferenceCenter for #name {
            type Params = #params_type;

            fn center_name() -> &'static str {
                #name_expr
            }
        }

        #affine_impl
    };

    Ok(expanded)
}

pub(crate) fn parse_center_attributes(input: &DeriveInput) -> syn::Result<CenterAttributes> {
    let mut attrs = CenterAttributes::default();

    for attr in &input.attrs {
        if attr.path().is_ident("center") {
            let nested = attr.parse_args_with(
                syn::punctuated::Punctuated::<Meta, syn::Token![,]>::parse_terminated,
            )?;

            for meta in nested {
                if let Meta::NameValue(nv) = meta {
                    if nv.path.is_ident("name") {
                        if let Expr::Lit(expr_lit) = &nv.value {
                            if let Lit::Str(lit_str) = &expr_lit.lit {
                                attrs.name = Some(lit_str.value());
                                continue;
                            }
                        }
                        return Err(syn::Error::new_spanned(
                            &nv.value,
                            "expected string literal for `name`",
                        ));
                    } else if nv.path.is_ident("params") {
                        if let Expr::Path(expr_path) = &nv.value {
                            attrs.params = Some(Type::Path(syn::TypePath {
                                qself: None,
                                path: expr_path.path.clone(),
                            }));
                            continue;
                        }
                        return Err(syn::Error::new_spanned(
                            &nv.value,
                            "expected type for `params`",
                        ));
                    } else if nv.path.is_ident("affine") {
                        if let Expr::Lit(expr_lit) = &nv.value {
                            if let Lit::Bool(lit_bool) = &expr_lit.lit {
                                attrs.affine = lit_bool.value();
                                continue;
                            }
                        }
                        return Err(syn::Error::new_spanned(
                            &nv.value,
                            "expected boolean for `affine`",
                        ));
                    }
                }
            }
        }
    }

    Ok(attrs)
}
