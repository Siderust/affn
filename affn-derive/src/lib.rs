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
//! - `#[frame(inherent)]` - Generate inherent methods on `Direction<F>` and `Position<C,F,U>`.
//!   Only valid when the frame is defined in the same crate as `Direction`/`Position`.
//! - `#[frame(ellipsoid = "Wgs84")]` - Also implement `HasEllipsoid` for the frame.
//!
//! ### `#[derive(ReferenceCenter)]`
//!
//! - `#[center(name = "CustomName")]` - Override the center name (defaults to struct name)
//! - `#[center(params = MyParamsType)]` - Specify the `Params` associated type (defaults to `()`)
//! - `#[center(affine = false)]` - Skip implementing `AffineCenter` marker trait

use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

mod center;
mod frame;

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
    match frame::derive_reference_frame_impl(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
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
    match center::derive_reference_center_impl(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}
