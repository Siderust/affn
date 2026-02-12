//! # Affine Operators Module
//!
//! This module provides pure mathematical operators for geometric transformations.
//! All types are domain-agnostic and contain no astronomy-specific vocabulary.
//!
//! ## Design Philosophy
//!
//! Operators in this module are:
//! - **Pure**: They perform only mathematical operations, no time-dependence or model selection.
//! - **Allocation-free**: All operations use stack-allocated storage.
//! - **Inline-friendly**: Heavily annotated with `#[inline]` for optimal performance.
//!
//! ## Operator Types
//!
//! - [`Rotation3`]: A 3x3 rotation matrix for pure orientation transforms.
//! - [`Translation3`]: A translation vector for pure center shifts.
//! - [`Isometry3`]: Combines rotation and translation for rigid body transforms.
//!
//! ## What These Types Do (and Don't Do)
//!
//! These operators are **untyped**: they work on raw `f64` vectors (`[f64; 3]`) and
//! `XYZ<f64>`. They intentionally do **not**:
//!
//! - track units (meters vs kilometers),
//! - pick reference frames/centers, or
//! - define the domain-specific meaning of a rotation/translation.
//!
//! Downstream crates typically wrap these operators with their own semantics and then
//! apply them to `affn` coordinate types.
//!
//! **Note**: translations apply to affine points (positions), not to free vectors
//! like directions.

mod isometry;
mod rotation;
mod translation;

pub use isometry::Isometry3;
pub use rotation::Rotation3;
pub use translation::Translation3;

use crate::cartesian::xyz::XYZ;
use qtty::{Quantity, Unit};

/// Generates `Mul<[Quantity<U>; 3]>` and `Mul<XYZ<Quantity<U>>>` implementations
/// for an affine operator type, eliminating boilerplate for unit-aware operations.
macro_rules! impl_quantity_mul {
    ($OpType:ty, $apply_fn:ident, $apply_xyz_fn:ident) => {
        impl<U: Unit> std::ops::Mul<[Quantity<U>; 3]> for $OpType {
            type Output = [Quantity<U>; 3];

            #[inline]
            fn mul(self, rhs: [Quantity<U>; 3]) -> [Quantity<U>; 3] {
                let [x, y, z] = self.$apply_fn([rhs[0].value(), rhs[1].value(), rhs[2].value()]);
                [Quantity::new(x), Quantity::new(y), Quantity::new(z)]
            }
        }

        impl<U: Unit> std::ops::Mul<XYZ<Quantity<U>>> for $OpType {
            type Output = XYZ<Quantity<U>>;

            #[inline]
            fn mul(self, rhs: XYZ<Quantity<U>>) -> XYZ<Quantity<U>> {
                XYZ::from_raw(self.$apply_xyz_fn(rhs.to_raw()))
            }
        }
    };
}

// Apply the macro to all three operator types
impl_quantity_mul!(Rotation3, apply_array, apply_xyz);
impl_quantity_mul!(Translation3, apply_array, apply_xyz);
impl_quantity_mul!(Isometry3, apply_point, apply_xyz);
