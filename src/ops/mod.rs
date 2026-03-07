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
//! ## Unit-Aware Operations
//!
//! All operators integrate seamlessly with [`qtty`] typed quantities and `affn`'s
//! coordinate types. The following `Mul` implementations are provided for each
//! operator:
//!
//! | Operand | Result | Use case |
//! |---------|--------|----------|
//! | `[Quantity<U>; 3]` | `[Quantity<U>; 3]` | Raw typed array rotation |
//! | `XYZ<Quantity<U>>` | `XYZ<Quantity<U>>` | Internal storage rotation |
//! | `Position<C, F, U>` | `Position<C, F, U>` | Rotate/translate an affine point |
//! | `Vector<F, U>` | `Vector<F, U>` | Rotate a free vector (rotation only) |
//! | `Direction<F>` | `Direction<F>` | Rotate a unit direction (rotation only) |
//!
//! Frame and center tags are preserved; the caller is responsible for
//! reinterpreting them after a transform (see [`Position::reinterpret_frame`]).
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
use crate::cartesian::{Direction, Position, Vector};
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::{LengthUnit, Quantity, Unit};

// =============================================================================
// Quantity-array and XYZ impls (all three operator types)
// =============================================================================

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

impl_quantity_mul!(Rotation3, apply_array, apply_xyz);
impl_quantity_mul!(Translation3, apply_array, apply_xyz);
impl_quantity_mul!(Isometry3, apply_point, apply_xyz);

// =============================================================================
// Coordinate-type impls: Position, Vector, Direction
// =============================================================================

/// Generates `Mul<Position<C,F,U>>` for an operator that transforms affine points.
///
/// The center, frame, and unit tags are preserved. The caller is responsible for
/// reinterpreting the frame tag after the transform.
macro_rules! impl_position_mul {
    ($OpType:ty, $apply_fn:ident) => {
        impl<C, F, U> std::ops::Mul<Position<C, F, U>> for $OpType
        where
            C: ReferenceCenter,
            F: ReferenceFrame,
            U: LengthUnit,
            C::Params: Clone,
        {
            type Output = Position<C, F, U>;

            #[inline]
            fn mul(self, rhs: Position<C, F, U>) -> Position<C, F, U> {
                let [x, y, z] = self.$apply_fn([rhs.x().value(), rhs.y().value(), rhs.z().value()]);
                Position::new_with_params(
                    rhs.center_params().clone(),
                    Quantity::<U>::new(x),
                    Quantity::<U>::new(y),
                    Quantity::<U>::new(z),
                )
            }
        }
    };
}

impl_position_mul!(Rotation3, apply_array);
impl_position_mul!(Translation3, apply_array);
impl_position_mul!(Isometry3, apply_point);

/// `Rotation3 * Vector<F, U>` — rotates a free vector, preserving frame and unit.
///
/// Translations do **not** apply to free vectors (they are translation-invariant),
/// so this is only implemented for `Rotation3`.
impl<F, U> std::ops::Mul<Vector<F, U>> for Rotation3
where
    F: ReferenceFrame,
    U: Unit,
{
    type Output = Vector<F, U>;

    #[inline]
    fn mul(self, rhs: Vector<F, U>) -> Vector<F, U> {
        let [x, y, z] = self.apply_array([rhs.x().value(), rhs.y().value(), rhs.z().value()]);
        Vector::new(
            Quantity::<U>::new(x),
            Quantity::<U>::new(y),
            Quantity::<U>::new(z),
        )
    }
}

/// `Rotation3 * Direction<F>` — rotates a unit direction, preserving frame.
///
/// Translations do **not** apply to directions; only rotation changes their
/// orientation. The result is guaranteed to remain a unit vector because
/// rotation preserves norms.
impl<F: ReferenceFrame> std::ops::Mul<Direction<F>> for Rotation3 {
    type Output = Direction<F>;

    #[inline]
    fn mul(self, rhs: Direction<F>) -> Direction<F> {
        let [x, y, z] = self.apply_array([rhs.x(), rhs.y(), rhs.z()]);
        // Rotation preserves norm → result is still unit-length.
        Direction::new_unchecked(x, y, z)
    }
}
