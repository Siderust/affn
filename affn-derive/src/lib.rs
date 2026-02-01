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
//! - `#[frame(polar = "dec", azimuth = "ra")]` - Also implement `SphericalNaming` with custom names
//! - `#[frame(distance = "altitude")]` - Override distance name (defaults to "distance")
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
///
/// ## SphericalNaming
///
/// When `polar` and `azimuth` attributes are provided, the macro also implements
/// [`SphericalNaming`](affn::frames::SphericalNaming):
///
/// ```rust,ignore
/// #[derive(Debug, Copy, Clone, ReferenceFrame)]
/// #[frame(polar = "dec", azimuth = "ra")]
/// struct ICRS;
///
/// assert_eq!(ICRS::polar_name(), "dec");
/// assert_eq!(ICRS::azimuth_name(), "ra");
/// assert_eq!(ICRS::distance_name(), "distance"); // default
/// ```
///
/// With custom distance name:
///
/// ```rust,ignore
/// #[derive(Debug, Copy, Clone, ReferenceFrame)]
/// #[frame(polar = "lat", azimuth = "lon", distance = "altitude")]
/// struct ITRF;
/// ```
#[proc_macro_derive(ReferenceFrame, attributes(frame))]
pub fn derive_reference_frame(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_reference_frame_impl(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Attributes parsed from `#[frame(...)]`.
#[derive(Default)]
struct FrameAttributes {
    /// Custom frame name (defaults to struct name).
    name: Option<String>,
    /// Polar angle name for SphericalNaming (e.g., "dec", "lat", "alt").
    polar: Option<String>,
    /// Azimuthal angle name for SphericalNaming (e.g., "ra", "lon", "az").
    azimuth: Option<String>,
    /// Distance name for SphericalNaming (defaults to "distance").
    distance: Option<String>,
}

fn derive_reference_frame_impl(input: DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;

    // Parse #[frame(...)] attributes
    let attrs = parse_frame_attributes(&input)?;

    let name_expr = match &attrs.name {
        Some(custom_name) => quote! { #custom_name },
        None => {
            let name_str = name.to_string();
            quote! { #name_str }
        }
    };

    // Generate SphericalNaming impl if both polar and azimuth are provided
    let spherical_impl = match (&attrs.polar, &attrs.azimuth) {
        (Some(polar), Some(azimuth)) => {
            let distance = attrs.distance.as_deref().unwrap_or("distance");
            quote! {
                impl ::affn::frames::SphericalNaming for #name {
                    fn polar_name() -> &'static str {
                        #polar
                    }
                    fn azimuth_name() -> &'static str {
                        #azimuth
                    }
                    fn distance_name() -> &'static str {
                        #distance
                    }
                }
            }
        }
        (Some(_), None) => {
            return Err(syn::Error::new_spanned(
                &input.ident,
                "`polar` attribute requires `azimuth` to also be specified",
            ));
        }
        (None, Some(_)) => {
            return Err(syn::Error::new_spanned(
                &input.ident,
                "`azimuth` attribute requires `polar` to also be specified",
            ));
        }
        (None, None) => quote! {},
    };

    let expanded = quote! {
        impl ::affn::frames::ReferenceFrame for #name {
            fn frame_name() -> &'static str {
                #name_expr
            }
        }

        #spherical_impl
    };

    Ok(expanded)
}

fn parse_frame_attributes(input: &DeriveInput) -> syn::Result<FrameAttributes> {
    let mut attrs = FrameAttributes::default();

    for attr in &input.attrs {
        if attr.path().is_ident("frame") {
            let nested = attr.parse_args_with(
                syn::punctuated::Punctuated::<Meta, syn::Token![,]>::parse_terminated,
            )?;

            for meta in nested {
                if let Meta::NameValue(nv) = meta {
                    let value_str = extract_string_literal(&nv.value)?;

                    if nv.path.is_ident("name") {
                        attrs.name = Some(value_str);
                    } else if nv.path.is_ident("polar") {
                        attrs.polar = Some(value_str);
                    } else if nv.path.is_ident("azimuth") {
                        attrs.azimuth = Some(value_str);
                    } else if nv.path.is_ident("distance") {
                        attrs.distance = Some(value_str);
                    }
                }
            }
        }
    }

    Ok(attrs)
}

/// Extract a string literal from an expression, or return an error.
fn extract_string_literal(expr: &Expr) -> syn::Result<String> {
    if let Expr::Lit(expr_lit) = expr {
        if let Lit::Str(lit_str) = &expr_lit.lit {
            return Ok(lit_str.value());
        }
    }
    Err(syn::Error::new_spanned(expr, "expected string literal"))
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
                    _ => {}
                }
            }
        }
    }

    Ok(attrs)
}
