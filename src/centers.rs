//! # Reference Centers Module
//!
//! This module defines the concept of a *reference center* (origin) for coordinate systems.
//! A reference center specifies the origin point from which positions are measured.
//!
//! ## Overview
//!
//! The [`ReferenceCenter`] trait provides a common interface for all reference center types.
//! Each center is represented as a zero-sized struct and implements the trait to provide
//! its canonical name.
//!
//! ## Domain-Agnostic Design
//!
//! This module provides **only** the trait infrastructure. Concrete center types
//! (e.g., astronomical centers, robotic bases, reference origins) should be defined
//! in domain-specific crates that depend on `affn`.
//!
//! ## Parameterized Centers
//!
//! Some reference centers require runtime parameters. For example, a "topocentric"
//! center in astronomy needs the observer's location. This is achieved through the
//! associated `Params` type on [`ReferenceCenter`]:
//!
//! - For most centers, `Params = ()` (zero-cost).
//! - For parameterized centers, `Params` stores the required data.
//!
//! ## Creating Custom Centers
//!
//! Use the derive macro for convenient definitions:
//!
//! ```rust
//! use affn::centers::ReferenceCenter;
//!
//! #[derive(Debug, Copy, Clone)]
//! pub struct MyCenter;
//!
//! impl ReferenceCenter for MyCenter {
//!     type Params = ();
//!     fn center_name() -> &'static str { "MyCenter" }
//! }
//!
//! assert_eq!(MyCenter::center_name(), "MyCenter");
//! ```
//!
//! For parameterized centers, implement the trait manually.
//!
//! ## Special Markers
//!
//! - [`NoCenter`]: Marker for translation-invariant objects (free vectors).
//! - [`AffineCenter`]: Marker trait for genuine spatial centers (not `NoCenter`).

use std::fmt::Debug;

/// A trait for defining a reference center (coordinate origin).
///
/// # Associated Types
///
/// - `Params`: Runtime parameters for this center. Use `()` for centers that
///   don't need parameters. For parameterized centers, this carries the required data.
///
/// # Implementing
///
/// ```rust
/// use affn::centers::ReferenceCenter;
///
/// #[derive(Debug, Copy, Clone)]
/// pub struct MyCenter;
///
/// impl ReferenceCenter for MyCenter {
///     type Params = ();
///     fn center_name() -> &'static str {
///         "MyCenter"
///     }
/// }
/// ```
pub trait ReferenceCenter: Copy + Clone + std::fmt::Debug {
    /// Runtime parameters for this center. Use `()` for centers that don't need parameters.
    type Params: Clone + Debug + Default + PartialEq;

    /// Returns the canonical name of this reference center.
    fn center_name() -> &'static str;
}

// =============================================================================
// Unit implementation (for generic code)
// =============================================================================

impl ReferenceCenter for () {
    type Params = ();

    fn center_name() -> &'static str {
        ""
    }
}

// =============================================================================
// NoCenter: Marker for translation-invariant (free) vectors
// =============================================================================

/// Marker type for translation-invariant (free) vectors.
///
/// Free vectors like directions and velocities do not have a meaningful
/// spatial origin. They represent properties that are independent of
/// any particular coordinate center:
///
/// - **Directions** are unit vectors representing orientations in space
/// - **Velocities** are rates of change that don't depend on position
///
/// Using `NoCenter` instead of a regular `ReferenceCenter` prevents
/// mathematically invalid center transformations at compile time.
/// Objects with `NoCenter` can only undergo frame transformations (rotations),
/// not center transformations (translations).
///
/// # Mathematical Rationale
///
/// In affine geometry:
/// - **Positions** are points in affine space; changing the origin (center) is a translation.
/// - **Directions** and **velocities** are elements of the underlying vector space;
///   they are translation-invariant and do not have an "origin" to change.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct NoCenter;

// NOTE: NoCenter deliberately does NOT implement ReferenceCenter or AffineCenter.
// This prevents center transformations on directions and velocities.

// =============================================================================
// AffineCenter: Marker for genuine spatial centers
// =============================================================================

/// Marker trait for types that represent genuine spatial centers (origins).
///
/// This trait is implemented only for center types that represent actual
/// coordinate origins. It is NOT implemented for `NoCenter`, which prevents
/// center transformations from being applied to free vectors (directions, velocities).
///
/// # Usage
///
/// Use this trait as a bound when implementing center transformations:
///
/// ```ignore
/// impl<F, U> TransformCenter<Position<C2, F, U>> for Position<C1, F, U>
/// where
///     C1: AffineCenter,
///     C2: AffineCenter,
///     // ...
/// ```
pub trait AffineCenter: ReferenceCenter {}

#[cfg(test)]
mod tests {
    use super::*;
    // Import the derives and traits
    use crate::DeriveReferenceCenter as ReferenceCenter;

    // Test with a locally defined center
    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct TestCenter;

    #[test]
    fn test_center_name() {
        assert_eq!(TestCenter::center_name(), "TestCenter");
        assert_eq!(<() as ReferenceCenter>::center_name(), "");
    }

    #[test]
    fn test_center_params_zero_size() {
        assert_eq!(
            std::mem::size_of::<<TestCenter as ReferenceCenter>::Params>(),
            0
        );
        assert_eq!(std::mem::size_of::<<() as ReferenceCenter>::Params>(), 0);
    }
}
