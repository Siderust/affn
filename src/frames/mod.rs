//! # Reference Frames Module
//!
//! This module defines the concept of a *reference frame* for coordinate systems.
//! A reference frame specifies the orientation of the axes used to describe positions in space.
//!
//! ## Overview
//!
//! The [`ReferenceFrame`] trait provides a common interface for all reference frame types.
//! Each frame is represented as a zero-sized struct and implements the trait to provide
//! its canonical name.
//!
//! ## Domain-Agnostic Design
//!
//! This module provides **only** the trait infrastructure. Concrete frame types
//! (e.g., astronomical frames, geographic frames, robotic frames) should be defined
//! in domain-specific crates that depend on `affn`.
//!
//! ## Creating Custom Frames
//!
//! Use the derive macro for convenient definitions:
//!
//! ```rust
//! use affn::frames::ReferenceFrame;
//!
//! #[derive(Debug, Copy, Clone)]
//! pub struct MyFrame;
//!
//! impl ReferenceFrame for MyFrame {
//!     fn frame_name() -> &'static str {
//!         "MyFrame"
//!     }
//! }
//! assert_eq!(MyFrame::frame_name(), "MyFrame");
//! ```

/// A trait for defining a reference frame (orientation).
///
/// Reference frames define the orientation of coordinate axes. Different frames
/// represent different ways of orienting a coordinate system (e.g., aligned with
/// an equator, an orbital plane, a horizon, etc.).
///
/// # Implementing
///
/// Implement this trait for zero-sized marker types that represent different frames:
///
/// ```rust
/// use affn::frames::ReferenceFrame;
///
/// #[derive(Debug, Copy, Clone)]
/// pub struct MyFrame;
///
/// impl ReferenceFrame for MyFrame {
///     fn frame_name() -> &'static str {
///         "MyFrame"
///     }
/// }
/// ```
pub trait ReferenceFrame: Copy + Clone + std::fmt::Debug {
    /// Returns the canonical name of this reference frame.
    fn frame_name() -> &'static str;
}

// =============================================================================
// Spherical Coordinate Naming Convention
// =============================================================================

/// Provides frame-specific names for spherical coordinate components.
///
/// This trait is used by serde implementations to serialize/deserialize
/// spherical coordinates with astronomically-appropriate field names.
///
/// # Default Implementation
///
/// The default implementation uses generic mathematical names:
/// - Polar angle: `"polar"`
/// - Azimuthal angle: `"azimuth"`
///
/// # Frame-Specific Names
///
/// Implement this trait on your frame types to use domain-specific names:
///
/// | Frame         | Polar Name | Azimuth Name |
/// |---------------|------------|--------------|
/// | Equatorial    | `"dec"`    | `"ra"`       |
/// | ICRS          | `"dec"`    | `"ra"`       |
/// | Ecliptic      | `"lat"`    | `"lon"`      |
/// | Horizontal    | `"alt"`    | `"az"`       |
/// | Geographic    | `"lat"`    | `"lon"`      |
/// | Galactic      | `"b"`      | `"l"`        |
/// | Supergalactic | `"sgb"`    | `"sgl"`      |
///
/// # Example
///
/// ```rust
/// use affn::frames::{ReferenceFrame, SphericalNaming};
///
/// #[derive(Debug, Copy, Clone)]
/// struct EclipticMeanJ2000;
///
/// impl ReferenceFrame for EclipticMeanJ2000 {
///     fn frame_name() -> &'static str { "EclipticMeanJ2000" }
/// }
///
/// impl SphericalNaming for EclipticMeanJ2000 {
///     fn polar_name() -> &'static str { "lat" }
///     fn azimuth_name() -> &'static str { "lon" }
/// }
/// ```
///
/// Types that don't implement this trait can use the default names via the
/// [`DefaultSphericalNaming`] helper.
pub trait SphericalNaming: ReferenceFrame {
    /// Returns the name for the polar/elevation angle (e.g., "dec", "lat", "alt", "b").
    fn polar_name() -> &'static str;

    /// Returns the name for the azimuthal angle (e.g., "ra", "lon", "az", "l").
    fn azimuth_name() -> &'static str;

    /// Returns the name for the radial distance (e.g., "distance", "altitude", "radius").
    ///
    /// Defaults to "distance" if not overridden.
    fn distance_name() -> &'static str {
        DefaultSphericalNaming::DISTANCE
    }
}

/// Helper type that provides default spherical naming (polar/azimuth).
///
/// Use this when you need spherical naming for a frame that doesn't implement
/// `SphericalNaming` directly.
pub struct DefaultSphericalNaming;

impl DefaultSphericalNaming {
    /// Default polar angle name.
    pub const POLAR: &'static str = "polar";
    /// Default azimuthal angle name.
    pub const AZIMUTH: &'static str = "azimuth";
    /// Default distance name.
    pub const DISTANCE: &'static str = "distance";
}

// =============================================================================
// Feature-gated astronomical frames
// =============================================================================

#[cfg(feature = "astro")]
mod astro;

#[cfg(feature = "astro")]
pub use astro::*;
