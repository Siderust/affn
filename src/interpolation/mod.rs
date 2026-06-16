//! Interpolation primitives for typed affine geometry.
//!
//! This module is domain-agnostic: it works over a scalar abscissa and complete
//! typed values. Astronomy-specific epoch handling belongs in downstream crates.

pub mod abscissa;
pub mod cubic_hermite;
pub mod error;
pub mod linear;
pub mod scalar;
pub mod traits;

pub use abscissa::InterpolationAbscissa;
pub use cubic_hermite::{
    CubicHermiteSpline, CubicHermiteTable, HermiteNode, HermiteSample, HermiteTableEvaluation,
    ScalarHermiteNode, ScalarHermiteTableEvaluation,
};
pub use error::InterpolationError;
pub use linear::linear_segment;
pub use scalar::{cubic_hermite_segment, HermiteEvaluation};
pub use traits::{HermiteBasis, HermiteInterpolable};
