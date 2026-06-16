//! Interpolation primitives for typed affine geometry.
//!
//! This module is domain-agnostic: it works over a scalar abscissa and complete
//! typed values. Astronomy-specific epoch handling belongs in downstream crates.

pub mod abscissa;
pub mod cubic_hermite;
pub mod error;
pub mod traits;

pub use abscissa::{AbscissaDelta, InterpolationAbscissa};
pub use cubic_hermite::{
    CubicHermiteTable, HermiteNode, HermiteTableEvaluation, ScalarCubicHermiteTable,
    ScalarHermiteNode, ScalarHermiteTableEvaluation,
};
pub use error::InterpolationError;
pub use traits::{HermiteBasis, HermiteInterpolable};
