//! Rigid body transformation (rotation + translation).

use super::{Rotation3, Translation3};
use crate::cartesian::xyz::XYZ;

/// A rigid body transformation combining rotation and translation.
///
/// An isometry preserves distances and angles. It consists of:
/// 1. A rotation component (`Rotation3`)
/// 2. A translation component (`Translation3`)
///
/// # Application Order
///
/// When applying an isometry to a point:
/// 1. First, the rotation is applied.
/// 2. Then, the translation is applied.
///
/// Mathematically: `p' = R * p + t`
///
/// # Sign Conventions for Center Transforms
///
/// When shifting from center C1 to center C2:
/// - The translation vector should be `pos(C2) - pos(C1)` expressed in the source frame.
/// - Apply as: `p_in_C2 = p_in_C1 - (C1_to_hub) = p_in_C1 + shift`
///   where `shift = -(C1_to_hub)` or equivalently `shift = hub_to_C1`.
///
/// **Convention adopted**: Translation is the position of the **new origin**
/// expressed in the **old frame**, negated. Or equivalently, the vector that
/// moves points FROM the old frame TO the new frame.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Isometry3 {
    /// The rotation component.
    pub rotation: Rotation3,
    /// The translation component (applied after rotation).
    pub translation: Translation3,
}

impl Isometry3 {
    /// The identity isometry (no transformation).
    pub const IDENTITY: Self = Self {
        rotation: Rotation3::IDENTITY,
        translation: Translation3::ZERO,
    };

    /// Creates a new isometry from rotation and translation.
    #[inline]
    pub const fn new(rotation: Rotation3, translation: Translation3) -> Self {
        Self {
            rotation,
            translation,
        }
    }

    /// Creates an isometry with only rotation (no translation).
    #[inline]
    pub const fn from_rotation(rotation: Rotation3) -> Self {
        Self {
            rotation,
            translation: Translation3::ZERO,
        }
    }

    /// Creates an isometry with only translation (no rotation).
    #[inline]
    pub const fn from_translation(translation: Translation3) -> Self {
        Self {
            rotation: Rotation3::IDENTITY,
            translation,
        }
    }

    /// Returns the inverse isometry.
    ///
    /// For `I = (R, t)`, the inverse is `I⁻¹ = (R⁻¹, -R⁻¹ * t)`.
    #[inline]
    pub fn inverse(&self) -> Self {
        let r_inv = self.rotation.inverse();
        let t_inv = r_inv.apply_array(self.translation.v);
        Self {
            rotation: r_inv,
            translation: Translation3::new(-t_inv[0], -t_inv[1], -t_inv[2]),
        }
    }

    /// Composes two isometries: `self * other`.
    ///
    /// The result applies `other` first, then `self`.
    /// For `I1 = (R1, t1)` and `I2 = (R2, t2)`:
    /// `I1 * I2 = (R1 * R2, R1 * t2 + t1)`
    #[inline]
    pub fn compose(&self, other: &Self) -> Self {
        let rotation = self.rotation.compose(&other.rotation);
        let rotated_t = self.rotation.apply_array(other.translation.v);
        let translation = Translation3::new(
            rotated_t[0] + self.translation.v[0],
            rotated_t[1] + self.translation.v[1],
            rotated_t[2] + self.translation.v[2],
        );
        Self {
            rotation,
            translation,
        }
    }

    /// Applies this isometry to a raw `[f64; 3]` array (as a point).
    ///
    /// Computes `R * p + t`.
    #[inline]
    pub fn apply_point(&self, p: [f64; 3]) -> [f64; 3] {
        let rotated = self.rotation.apply_array(p);
        self.translation.apply_array(rotated)
    }

    /// Applies this isometry to an `XYZ<f64>` (as a point).
    #[inline]
    pub fn apply_xyz(&self, xyz: XYZ<f64>) -> XYZ<f64> {
        let [x, y, z] = self.apply_point([xyz.x(), xyz.y(), xyz.z()]);
        XYZ::new(x, y, z)
    }

    /// Applies only the rotation component (for vectors/directions).
    ///
    /// Use this for free vectors that are translation-invariant.
    #[inline]
    pub fn apply_vector(&self, v: [f64; 3]) -> [f64; 3] {
        self.rotation.apply_array(v)
    }

    /// Applies only the rotation component to an `XYZ<f64>`.
    #[inline]
    pub fn apply_vector_xyz(&self, xyz: XYZ<f64>) -> XYZ<f64> {
        self.rotation.apply_xyz(xyz)
    }
}

impl Default for Isometry3 {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl std::ops::Mul for Isometry3 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        self.compose(&rhs)
    }
}

/// Applies an isometry (rotation + translation) to a raw `[f64; 3]` point: `R * p + t`.
impl std::ops::Mul<[f64; 3]> for Isometry3 {
    type Output = [f64; 3];

    #[inline]
    fn mul(self, rhs: [f64; 3]) -> [f64; 3] {
        self.apply_point(rhs)
    }
}

// Mul<[Quantity<U>; 3]> and Mul<XYZ<Quantity<U>>> are generated
// by impl_quantity_mul! in the parent module.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cartesian::xyz::XYZ;
    use qtty::Radians;
    use std::f64::consts::FRAC_PI_2;

    const EPSILON: f64 = 1e-12;

    fn assert_array_eq(a: [f64; 3], b: [f64; 3], msg: &str) {
        assert!(
            (a[0] - b[0]).abs() < EPSILON
                && (a[1] - b[1]).abs() < EPSILON
                && (a[2] - b[2]).abs() < EPSILON,
            "{}: {:?} != {:?}",
            msg,
            a,
            b
        );
    }

    #[test]
    fn test_isometry_identity() {
        let iso = Isometry3::IDENTITY;
        let p = [1.0, 2.0, 3.0];
        assert_array_eq(
            iso.apply_point(p),
            p,
            "Identity isometry should not change point",
        );
    }

    #[test]
    fn test_isometry_rotation_only() {
        let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
        let iso = Isometry3::from_rotation(rot);

        let p = [1.0, 0.0, 0.0];
        let result = iso.apply_point(p);
        assert_array_eq(result, [0.0, 1.0, 0.0], "Rotation-only isometry");
    }

    #[test]
    fn test_isometry_translation_only() {
        let trans = Translation3::new(1.0, 2.0, 3.0);
        let iso = Isometry3::from_translation(trans);

        let p = [0.0, 0.0, 0.0];
        let result = iso.apply_point(p);
        assert_array_eq(result, [1.0, 2.0, 3.0], "Translation-only isometry");
    }

    #[test]
    fn test_isometry_combined() {
        let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
        let trans = Translation3::new(1.0, 0.0, 0.0);
        let iso = Isometry3::new(rot, trans);

        let p = [1.0, 0.0, 0.0];
        let result = iso.apply_point(p);
        assert_array_eq(result, [1.0, 1.0, 0.0], "Combined isometry");
    }

    #[test]
    fn test_isometry_inverse() {
        let rot = Rotation3::rz(Radians::new(0.5));
        let trans = Translation3::new(1.0, 2.0, 3.0);
        let iso = Isometry3::new(rot, trans);
        let iso_inv = iso.inverse();

        let p = [4.0, 5.0, 6.0];
        let transformed = iso.apply_point(p);
        let recovered = iso_inv.apply_point(transformed);
        assert_array_eq(recovered, p, "Isometry inverse should recover original");
    }

    #[test]
    fn test_isometry_composition() {
        let iso1 = Isometry3::new(
            Rotation3::rz(Radians::new(FRAC_PI_2)),
            Translation3::new(1.0, 0.0, 0.0),
        );
        let iso2 = Isometry3::new(
            Rotation3::rx(Radians::new(FRAC_PI_2)),
            Translation3::new(0.0, 1.0, 0.0),
        );

        let composed = iso1.compose(&iso2);
        let p = [0.0, 0.0, 0.0];

        let result = composed.apply_point(p);
        assert_array_eq(result, [0.0, 0.0, 0.0], "Composed isometry");
    }

    #[test]
    fn test_isometry_apply_vector() {
        let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
        let trans = Translation3::new(100.0, 200.0, 300.0);
        let iso = Isometry3::new(rot, trans);

        let v = [1.0, 0.0, 0.0];
        let result = iso.apply_vector(v);
        assert_array_eq(result, [0.0, 1.0, 0.0], "Vector ignores translation");
    }

    #[test]
    fn test_isometry_helpers_and_ops() {
        let iso = Isometry3::default();
        assert_eq!(iso, Isometry3::IDENTITY);

        let iso1 = Isometry3::new(
            Rotation3::rz(Radians::new(FRAC_PI_2)),
            Translation3::new(1.0, 0.0, 0.0),
        );
        let iso2 = Isometry3::from_translation(Translation3::new(0.0, 1.0, 0.0));
        let composed = iso1 * iso2;

        let p = XYZ::new(1.0, 0.0, 0.0);
        let applied = composed.apply_xyz(p);
        assert_array_eq(
            [applied.x(), applied.y(), applied.z()],
            [0.0, 1.0, 0.0],
            "apply_xyz",
        );

        let v = XYZ::new(1.0, 0.0, 0.0);
        let vec_only = composed.apply_vector_xyz(v);
        assert_array_eq(
            [vec_only.x(), vec_only.y(), vec_only.z()],
            [0.0, 1.0, 0.0],
            "apply_vector_xyz",
        );
    }

    #[test]
    fn test_isometry_mul_f64_array() {
        let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
        let trans = Translation3::new(1.0, 0.0, 0.0);
        let iso = Isometry3::new(rot, trans);
        let result = iso * [1.0, 0.0, 0.0];
        assert_array_eq(result, [1.0, 1.0, 0.0], "Isometry * [f64; 3]");
    }

    #[test]
    fn test_isometry_mul_quantity_array() {
        use qtty::{Meter, Quantity};
        let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
        let trans = Translation3::new(1.0, 0.0, 0.0);
        let iso = Isometry3::new(rot, trans);
        let v = [
            Quantity::<Meter>::new(1.0),
            Quantity::<Meter>::new(0.0),
            Quantity::<Meter>::new(0.0),
        ];
        let result = iso * v;
        assert!((result[0].value() - 1.0).abs() < EPSILON);
        assert!((result[1].value() - 1.0).abs() < EPSILON);
        assert!((result[2].value()).abs() < EPSILON);
    }
}
