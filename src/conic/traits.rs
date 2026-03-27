//! Shared sealed traits for conic markers and validated shape types.

use std::fmt;

use super::{sealed, ConicKind};

/// Sealed trait implemented by all three kind markers.
pub trait KindMarker: sealed::KindMarkerSealed + Copy + Clone + fmt::Debug {
    /// The `ConicKind` value associated with this marker.
    fn conic_kind() -> ConicKind;
}

/// Sealed trait implemented by non-parabolic kind markers (`Elliptic`, `Hyperbolic`).
///
/// `SemiMajorAxisParam` is only valid for these kinds; this bound enforces that
/// at compile time.
pub trait NonParabolicKindMarker: KindMarker {}

/// Sealed trait for validated conic shape parameterisations.
///
/// Only `PeriapsisParam`, `SemiMajorAxisParam`, `TypedPeriapsisParam`, and
/// `TypedSemiMajorAxisParam` implement this trait. Because all shapes are
/// validated at construction time, `kind()` is infallible.
pub trait ConicShape: sealed::ConicShapeSealed + Copy + Clone + fmt::Debug {
    /// Human-readable name for the characteristic length field.
    fn shape_name() -> &'static str;

    /// The orbital eccentricity stored in this shape.
    fn eccentricity(&self) -> f64;

    /// Classifies the conic from its eccentricity. Always succeeds on a
    /// validly-constructed shape.
    fn kind(&self) -> ConicKind;
}
