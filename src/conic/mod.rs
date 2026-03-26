//! Domain-agnostic conic geometry primitives.
//!
//! These types capture reusable geometric properties of conic sections without
//! introducing any time or propagation semantics.
//!
//! ## Two-Layer Design
//!
//! ### Erased (runtime) layer
//! - [`PeriapsisParam<U>`] - periapsis-distance parameterisation; valid for all conic kinds.
//! - [`SemiMajorAxisParam<U>`] - semi-major-axis parameterisation; rejects parabolic (`e == 1`) at
//!   construction.
//! - [`ConicOrientation<F>`] - 3-D orientation tagged with a [`ReferenceFrame`].
//! - [`OrientedConic<S, F>`] - unified oriented conic, generic over shape and frame.
//!
//! All erased shapes are validated at construction time via `try_new(...)` constructors.
//! After construction `kind()` is infallible.
//!
//! ### Typed (kind-specific) layer
//! - Marker types [`Elliptic`], [`Parabolic`], [`Hyperbolic`] and their sealing traits.
//! - [`TypedPeriapsisParam<U, K>`] - periapsis parameterisation branded with a kind marker.
//! - [`TypedSemiMajorAxisParam<U, K>`] - semi-major-axis parameterisation branded with a
//!   non-parabolic kind marker.
//! - Kind-specific aliases such as [`EllipticPeriapsis<U, F>`] and
//!   [`EllipticSemiMajorAxis<U, F>`] for the most common typed oriented forms.
//! - [`ClassifiedPeriapsisParam<U>`] / [`ClassifiedSemiMajorAxisParam<U>`] - runtime
//!   classification results returned by `classify()`.
//!
//! ## Const path
//! For compile-time body constants use the `new_unchecked` constructors which skip runtime
//! validation. Callers are responsible for supplying valid values.

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
