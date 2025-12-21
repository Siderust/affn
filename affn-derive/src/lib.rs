//! # affn-derive
//!
//! Derive macros for the `affn` crate, providing `#[derive(ReferenceFrame)]`
//! and `#[derive(ReferenceCenter)]` for convenient frame and center definitions.
//!
//! ## Usage
//!
//! These derives are re-exported from `affn`, so you typically use them as:
//!
//! ```rust,ignore
//! use affn::{ReferenceFrame, ReferenceCenter};
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct MyFrame;
//!
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct MyCenter;
//! ```
//!
//! ## Attributes
//!
//! ### `#[derive(ReferenceFrame)]`
//!
//! - `#[frame(name = "CustomName")]` - Override the frame name (defaults to struct name)
//!
//! ### `#[derive(ReferenceCenter)]`
//!
//! - `#[center(name = "CustomName")]` - Override the center name (defaults to struct name)
//! - `#[center(params = MyParamsType)]` - Specify the `Params` associated type (defaults to `()`)
//! - `#[center(affine = false)]` - Skip implementing `AffineCenter` marker trait

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Expr, Lit, Meta, Type};

// =============================================================================
// ReferenceFrame derive
// =============================================================================

/// Derive macro for implementing [`ReferenceFrame`](affn::frames::ReferenceFrame).
///
/// # Example
///
/// ```rust,ignore
/// use affn::ReferenceFrame;
///
/// #[derive(Debug, Copy, Clone, ReferenceFrame)]
/// struct ICRS;
///
/// assert_eq!(ICRS::frame_name(), "ICRS");
/// ```
///
/// ## Custom Name
///
/// ```rust,ignore
/// #[derive(Debug, Copy, Clone, ReferenceFrame)]
/// #[frame(name = "International Celestial Reference System")]
/// struct ICRS;
///
/// assert_eq!(ICRS::frame_name(), "International Celestial Reference System");
/// ```
#[proc_macro_derive(ReferenceFrame, attributes(frame))]
pub fn derive_reference_frame(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_reference_frame_impl(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn derive_reference_frame_impl(input: DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;

    // Parse #[frame(name = "...")] attribute if present
    let frame_name = parse_frame_attribute(&input)?;

    let name_expr = match frame_name {
        Some(custom_name) => quote! { #custom_name },
        None => {
            let name_str = name.to_string();
            quote! { #name_str }
        }
    };

    let expanded = quote! {
        impl ::affn::frames::ReferenceFrame for #name {
            fn frame_name() -> &'static str {
                #name_expr
            }
        }
    };

    Ok(expanded)
}

fn parse_frame_attribute(input: &DeriveInput) -> syn::Result<Option<String>> {
    for attr in &input.attrs {
        if attr.path().is_ident("frame") {
            let nested = attr.parse_args_with(
                syn::punctuated::Punctuated::<Meta, syn::Token![,]>::parse_terminated,
            )?;

            for meta in nested {
                if let Meta::NameValue(nv) = meta {
                    if nv.path.is_ident("name") {
                        if let Expr::Lit(expr_lit) = &nv.value {
                            if let Lit::Str(lit_str) = &expr_lit.lit {
                                return Ok(Some(lit_str.value()));
                            }
                        }
                        return Err(syn::Error::new_spanned(
                            &nv.value,
                            "expected string literal for `name`",
                        ));
                    }
                }
            }
        }
    }
    Ok(None)
}

// =============================================================================
// ReferenceCenter derive
// =============================================================================

/// Derive macro for implementing [`ReferenceCenter`](affn::centers::ReferenceCenter).
///
/// By default, this also implements [`AffineCenter`](affn::centers::AffineCenter).
///
/// # Example
///
/// ```rust,ignore
/// use affn::ReferenceCenter;
///
/// #[derive(Debug, Copy, Clone, ReferenceCenter)]
/// struct Heliocentric;
///
/// assert_eq!(Heliocentric::center_name(), "Heliocentric");
/// ```
///
/// ## Custom Parameters
///
/// ```rust,ignore
/// use affn::ReferenceCenter;
///
/// #[derive(Clone, Debug, Default, PartialEq)]
/// struct ObserverLocation {
///     lat: f64,
///     lon: f64,
/// }
///
/// #[derive(Debug, Copy, Clone, ReferenceCenter)]
/// #[center(params = ObserverLocation)]
/// struct Topocentric;
/// ```
///
/// ## Skip AffineCenter
///
/// ```rust,ignore
/// #[derive(Debug, Copy, Clone, ReferenceCenter)]
/// #[center(affine = false)]
/// struct NonAffineCenter;
/// ```
#[proc_macro_derive(ReferenceCenter, attributes(center))]
pub fn derive_reference_center(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_reference_center_impl(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

struct CenterAttributes {
    name: Option<String>,
    params: Option<Type>,
    affine: bool,
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

fn derive_reference_center_impl(input: DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;

    // Parse #[center(...)] attributes
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

fn parse_center_attributes(input: &DeriveInput) -> syn::Result<CenterAttributes> {
    let mut attrs = CenterAttributes::default();

    for attr in &input.attrs {
        if attr.path().is_ident("center") {
            let nested = attr.parse_args_with(
                syn::punctuated::Punctuated::<Meta, syn::Token![,]>::parse_terminated,
            )?;

            for meta in nested {
                match meta {
                    Meta::NameValue(nv) => {
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
                            // Parse as a type path
                            if let Expr::Path(expr_path) = &nv.value {
                                attrs.params =
                                    Some(Type::Path(syn::TypePath { qself: None, path: expr_path.path.clone() }));
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
                    _ => {}
                }
            }
        }
    }

    Ok(attrs)
}
