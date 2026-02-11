//! Translation vector operator.

use crate::cartesian::xyz::XYZ;

/// A translation vector in 3D space.
///
/// This is a pure mathematical operator representing a displacement.
/// Frame and unit semantics are handled by the caller.
///
/// # Usage
///
/// Translations apply only to positions (affine points), not to directions
/// or vectors (which are translation-invariant).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Translation3 {
    /// The translation vector components.
    pub v: [f64; 3],
}

impl Translation3 {
    /// Zero translation (no displacement).
    pub const ZERO: Self = Self { v: [0.0, 0.0, 0.0] };

    /// Creates a new translation from components.
    #[inline]
    pub const fn new(x: f64, y: f64, z: f64) -> Self {
        Self { v: [x, y, z] }
    }

    /// Creates a translation from an array.
    #[inline]
    pub const fn from_array(v: [f64; 3]) -> Self {
        Self { v }
    }

    /// Creates a translation from an `XYZ<f64>`.
    #[inline]
    pub fn from_xyz(xyz: XYZ<f64>) -> Self {
        Self::new(xyz.x(), xyz.y(), xyz.z())
    }

    /// Returns the inverse translation.
    #[inline]
    pub fn inverse(&self) -> Self {
        Self::new(-self.v[0], -self.v[1], -self.v[2])
    }

    /// Composes two translations: `self + other`.
    #[inline]
    pub fn compose(&self, other: &Self) -> Self {
        Self::new(
            self.v[0] + other.v[0],
            self.v[1] + other.v[1],
            self.v[2] + other.v[2],
        )
    }

    /// Applies this translation to a raw `[f64; 3]` array.
    #[inline]
    pub fn apply_array(&self, v: [f64; 3]) -> [f64; 3] {
        [v[0] + self.v[0], v[1] + self.v[1], v[2] + self.v[2]]
    }

    /// Applies this translation to an `XYZ<f64>`.
    #[inline]
    pub fn apply_xyz(&self, xyz: XYZ<f64>) -> XYZ<f64> {
        let [x, y, z] = self.apply_array([xyz.x(), xyz.y(), xyz.z()]);
        XYZ::new(x, y, z)
    }

    /// Returns the translation as an array.
    #[inline]
    pub const fn as_array(&self) -> &[f64; 3] {
        &self.v
    }

    /// Returns the translation as an `XYZ<f64>`.
    #[inline]
    pub fn as_xyz(&self) -> XYZ<f64> {
        XYZ::new(self.v[0], self.v[1], self.v[2])
    }
}

impl Default for Translation3 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl std::ops::Add for Translation3 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        self.compose(&rhs)
    }
}

impl std::ops::Neg for Translation3 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.inverse()
    }
}

/// Applies a translation to a raw `[f64; 3]` point: `p + t`.
impl std::ops::Mul<[f64; 3]> for Translation3 {
    type Output = [f64; 3];

    #[inline]
    fn mul(self, rhs: [f64; 3]) -> [f64; 3] {
        self.apply_array(rhs)
    }
}

// Mul<[Quantity<U>; 3]> and Mul<XYZ<Quantity<U>>> are generated
// by impl_quantity_mul! in the parent module.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cartesian::xyz::XYZ;

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
    fn test_translation_zero() {
        let t = Translation3::ZERO;
        let v = [1.0, 2.0, 3.0];
        assert_array_eq(
            t.apply_array(v),
            v,
            "Zero translation should not change point",
        );
    }

    #[test]
    fn test_translation_apply() {
        let t = Translation3::new(1.0, 2.0, 3.0);
        let p = [0.0, 0.0, 0.0];
        assert_array_eq(
            t.apply_array(p),
            [1.0, 2.0, 3.0],
            "Translation should offset point",
        );
    }

    #[test]
    fn test_translation_inverse() {
        let t = Translation3::new(1.0, 2.0, 3.0);
        let t_inv = t.inverse();
        let p = [0.0, 0.0, 0.0];
        let result = t_inv.apply_array(t.apply_array(p));
        assert_array_eq(result, p, "T * T^-1 should return to origin");
    }

    #[test]
    fn test_translation_compose() {
        let t1 = Translation3::new(1.0, 0.0, 0.0);
        let t2 = Translation3::new(0.0, 1.0, 0.0);
        let composed = t1.compose(&t2);
        let p = [0.0, 0.0, 0.0];
        assert_array_eq(
            composed.apply_array(p),
            [1.0, 1.0, 0.0],
            "Composed translation",
        );
    }

    #[test]
    fn test_translation_helpers_and_ops() {
        let t = Translation3::from_array([1.0, 2.0, 3.0]);
        assert_eq!(t.as_array(), &[1.0, 2.0, 3.0]);
        let xyz = XYZ::new(1.0, 2.0, 3.0);
        let from_xyz = Translation3::from_xyz(xyz);
        assert_eq!(from_xyz, t);

        let applied = t.apply_xyz(XYZ::new(0.0, 0.0, 0.0));
        assert_array_eq(
            [applied.x(), applied.y(), applied.z()],
            [1.0, 2.0, 3.0],
            "apply_xyz",
        );

        let sum = t + Translation3::new(1.0, 0.0, 0.0);
        assert_eq!(sum.as_array(), &[2.0, 2.0, 3.0]);
        let neg = -t;
        assert_eq!(neg.as_array(), &[-1.0, -2.0, -3.0]);

        let default = Translation3::default();
        assert_eq!(default, Translation3::ZERO);
        let as_xyz = t.as_xyz();
        assert_array_eq(
            [as_xyz.x(), as_xyz.y(), as_xyz.z()],
            [1.0, 2.0, 3.0],
            "as_xyz",
        );
    }

    #[test]
    fn test_translation_mul_f64_array() {
        let t = Translation3::new(1.0, 2.0, 3.0);
        let result = t * [0.0, 0.0, 0.0];
        assert_array_eq(result, [1.0, 2.0, 3.0], "Translation * [f64; 3]");
    }

    #[test]
    fn test_translation_mul_quantity_array() {
        use qtty::{Meter, Quantity};
        let t = Translation3::new(1.0, 2.0, 3.0);
        let v = [
            Quantity::<Meter>::new(10.0),
            Quantity::<Meter>::new(20.0),
            Quantity::<Meter>::new(30.0),
        ];
        let result = t * v;
        assert!((result[0].value() - 11.0).abs() < EPSILON);
        assert!((result[1].value() - 22.0).abs() < EPSILON);
        assert!((result[2].value() - 33.0).abs() < EPSILON);
    }
}
