//! Domain-agnostic conic geometry primitives.
//!
//! This module models conic-section shape and orientation without introducing
//! time scales, central bodies, or propagation semantics. It is the reusable
//! geometry layer that higher-level orbit or trajectory code can build on.
//!
//! ## Model
//!
//! A conic in `affn` has two independent parts:
//! - a validated shape parameterisation, carrying one characteristic length in a
//!   `qtty` unit plus an eccentricity `e`;
//! - a [`ConicOrientation<F>`] tagged with a
//!   [`ReferenceFrame`](crate::frames::ReferenceFrame), describing the 3-D
//!   orientation of the conic plane and periapsis direction.
//!
//! [`OrientedConic<S, F>`] simply combines those two validated values.
//!
//! ## Choosing a shape type
//!
//! Use the erased runtime forms when the conic kind is not yet known:
//! - [`PeriapsisParam<U>`] stores periapsis distance `q` and supports elliptic,
//!   parabolic, and hyperbolic shapes.
//! - [`SemiMajorAxisParam<U>`] stores semi-major axis `a` and supports only
//!   non-parabolic shapes, so `try_new(...)` rejects `e == 1`.
//!
//! After validation, [`ConicShape::kind`] is infallible on either erased type.
//!
//! Use the typed forms when an API needs the conic family encoded in the type:
//! - [`TypedPeriapsisParam<U, K>`] brands a periapsis-based shape with
//!   [`Elliptic`], [`Parabolic`], or [`Hyperbolic`].
//! - [`TypedSemiMajorAxisParam<U, K>`] brands a semi-major-axis shape with a
//!   non-parabolic kind marker.
//! - [`ClassifiedPeriapsisParam<U>`] and [`ClassifiedSemiMajorAxisParam<U>`]
//!   are the runtime classification results returned by `classify()`.
//! - Aliases such as [`EllipticPeriapsis<U, F>`] and
//!   [`HyperbolicSemiMajorAxis<U, F>`] package the most common typed
//!   [`OrientedConic`] forms.
//!
//! ## Conversion Rules
//!
//! The shape conversions preserve eccentricity:
//! - [`PeriapsisParam::to_semi_major_axis`] and the corresponding oriented
//!   conversions return `None` for parabolic shapes because a semi-major axis is
//!   undefined at `e == 1`.
//! - [`SemiMajorAxisParam::to_periapsis`] and the corresponding oriented
//!   conversions return `None` only when the derived periapsis distance
//!   overflows or becomes non-finite.
//! - Oriented conversions always preserve the reference-frame tag and the
//!   existing [`ConicOrientation<F>`].
//!
//! ## Validation And `const` Construction
//!
//! Prefer `try_new(...)` in normal code so invalid distances, eccentricities,
//! and orientation angles are rejected immediately.
//!
//! For compile-time constants, `new_unchecked(...)` constructors are available
//! and skip validation. They are intended only for values whose invariants are
//! already guaranteed by the caller.
//!
//! ## Example
//!
//! ```rust
//! use affn::conic::{
//!     ClassifiedPeriapsisParam, ConicKind, ConicOrientation, ConicShape,
//!     OrientedConic, PeriapsisParam,
//! };
//! use affn::frames::ReferenceFrame;
//! use qtty::units::*; use qtty::{Quantity, M, KM, DEG, RAD, SEC, AU, LY}; use qtty::angular::{Degrees, Radians}; use qtty::length::{Meters, Kilometers};
//!
//! #[derive(Debug, Copy, Clone, PartialEq)]
//! struct Inertial;
//!
//! impl ReferenceFrame for Inertial {
//!     fn frame_name() -> &'static str {
//!         "Inertial"
//!     }
//! }
//!
//! let shape = PeriapsisParam::try_new(7_000.0 * M, 0.42)?;
//! assert_eq!(shape.kind(), ConicKind::Elliptic);
//!
//! let ClassifiedPeriapsisParam::Elliptic(typed_shape) = shape.classify() else {
//!     unreachable!("0.42 is elliptic");
//! };
//!
//! let orientation =
//!     ConicOrientation::<Inertial>::try_new(28.5 * DEG, 40.0 * DEG, 15.0 * DEG)?;
//! let conic = OrientedConic::new(typed_shape, orientation);
//! let sma = conic
//!     .to_semi_major_axis()
//!     .expect("elliptic conics convert to semi-major-axis form");
//!
//! assert_eq!(sma.kind(), ConicKind::Elliptic);
//! assert_eq!(sma.orientation(), conic.orientation());
//! # Ok::<(), affn::conic::ConicValidationError>(())
//! ```

mod sealed {
    pub trait ConicShapeSealed {}
    pub trait KindMarkerSealed {}
}

mod errors;
mod kind;
mod traits;

mod elliptic;
mod hyperbolic;
mod parabolic;

mod internal;

mod orientation;
mod oriented;
mod periapsis;
mod semi_major_axis;

pub use errors::ConicValidationError;
pub use kind::ConicKind;
pub use traits::{ConicShape, KindMarker, NonParabolicKindMarker};

pub use elliptic::Elliptic;
pub use hyperbolic::Hyperbolic;
pub use parabolic::Parabolic;

pub use orientation::ConicOrientation;
pub use oriented::OrientedConic;
pub use periapsis::{ClassifiedPeriapsisParam, PeriapsisParam, TypedPeriapsisParam};
pub use semi_major_axis::{
    ClassifiedSemiMajorAxisParam, SemiMajorAxisParam, TypedSemiMajorAxisParam,
};

/// Shorthand for an elliptic oriented conic expressed with periapsis distance.
pub type EllipticPeriapsis<U, F> = OrientedConic<TypedPeriapsisParam<U, Elliptic>, F>;

/// Shorthand for a parabolic oriented conic expressed with periapsis distance.
pub type ParabolicPeriapsis<U, F> = OrientedConic<TypedPeriapsisParam<U, Parabolic>, F>;

/// Shorthand for a hyperbolic oriented conic expressed with periapsis distance.
pub type HyperbolicPeriapsis<U, F> = OrientedConic<TypedPeriapsisParam<U, Hyperbolic>, F>;

/// Shorthand for an elliptic oriented conic expressed with semi-major axis.
pub type EllipticSemiMajorAxis<U, F> = OrientedConic<TypedSemiMajorAxisParam<U, Elliptic>, F>;

/// Shorthand for a hyperbolic oriented conic expressed with semi-major axis.
pub type HyperbolicSemiMajorAxis<U, F> = OrientedConic<TypedSemiMajorAxisParam<U, Hyperbolic>, F>;

#[cfg(test)]
mod tests;
