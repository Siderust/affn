//! Interpolation primitives for typed affine geometry.
//!
//! This module is domain-agnostic: it works over a scalar abscissa and complete
//! typed values. Astronomy-specific epoch handling belongs in downstream crates.

pub mod cubic_hermite;
pub mod error;
pub mod linear;
pub mod quantity;
pub mod scalar;
pub mod traits;

pub use cubic_hermite::{
    CubicHermiteSpline, CubicHermiteTable, HermiteNode, HermiteSample, HermiteTableEvaluation,
};
pub use error::InterpolationError;
pub use linear::linear_segment;
pub use quantity::{
    CubicHermiteQuantityTable, QuantityHermiteInterpolable, QuantityHermiteNode,
    QuantityHermiteTableEvaluation,
};
pub use scalar::{cubic_hermite_segment, HermiteEvaluation};
pub use traits::HermiteInterpolable;
