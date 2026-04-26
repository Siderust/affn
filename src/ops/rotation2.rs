//! 2D rotation operator.

use qtty::angular::Radians;

/// A 2x2 rotation matrix for planar orientation transforms.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Rotation2 {
    m: [[f64; 2]; 2],
}

impl Rotation2 {
    /// The identity rotation.
    pub const IDENTITY: Self = Self {
        m: [[1.0, 0.0], [0.0, 1.0]],
    };

    /// Creates a rotation matrix from raw row-major data.
    #[inline]
    #[must_use]
    pub const fn from_matrix(m: [[f64; 2]; 2]) -> Self {
        Self { m }
    }

    /// Creates a 2D counter-clockwise rotation.
    #[inline]
    #[must_use]
    pub fn new(angle: Radians) -> Self {
        let (s, c) = angle.sin_cos();
        Self {
            m: [[c, -s], [s, c]],
        }
    }

    /// Returns the transpose, which is the inverse for a rotation matrix.
    #[inline]
    #[must_use]
    pub fn transpose(&self) -> Self {
        Self {
            m: [[self.m[0][0], self.m[1][0]], [self.m[0][1], self.m[1][1]]],
        }
    }

    /// Returns the inverse rotation.
    #[inline]
    #[must_use]
    pub fn inverse(&self) -> Self {
        self.transpose()
    }

    /// Composes two rotations. The result applies `other` first, then `self`.
    #[inline]
    #[must_use]
    pub fn compose(&self, other: &Self) -> Self {
        *self * *other
    }

    /// Applies this rotation to a raw `[f64; 2]` column vector.
    #[inline]
    #[must_use]
    pub fn apply_array(&self, v: [f64; 2]) -> [f64; 2] {
        [
            self.m[0][0] * v[0] + self.m[0][1] * v[1],
            self.m[1][0] * v[0] + self.m[1][1] * v[1],
        ]
    }

    /// Returns the underlying row-major matrix.
    #[inline]
    #[must_use]
    pub const fn as_matrix(&self) -> &[[f64; 2]; 2] {
        &self.m
    }
}

impl Default for Rotation2 {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl core::ops::Mul for Rotation2 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let m = self
            .m
            .map(|row| core::array::from_fn(|j| row[0] * rhs.m[0][j] + row[1] * rhs.m[1][j]));
        Self { m }
    }
}

impl core::ops::Mul<[f64; 2]> for Rotation2 {
    type Output = [f64; 2];

    #[inline]
    fn mul(self, rhs: [f64; 2]) -> Self::Output {
        self.apply_array(rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::angular::Radians;
    use std::f64::consts::{FRAC_PI_2, PI};

    fn approx_eq(a: f64, b: f64) -> bool {
        (a - b).abs() < 1e-12
    }

    fn approx_eq_arr(a: [f64; 2], b: [f64; 2]) -> bool {
        approx_eq(a[0], b[0]) && approx_eq(a[1], b[1])
    }

    #[test]
    fn identity_is_default() {
        let id: Rotation2 = Default::default();
        assert_eq!(id, Rotation2::IDENTITY);
    }

    #[test]
    fn from_matrix_round_trip() {
        let m = [[0.0_f64, -1.0], [1.0, 0.0]];
        let r = Rotation2::from_matrix(m);
        assert_eq!(r.as_matrix(), &m);
    }

    #[test]
    fn new_90_deg_rotation() {
        let r = Rotation2::new(Radians::new(FRAC_PI_2));
        let result = r.apply_array([1.0, 0.0]);
        assert!(approx_eq(result[0], 0.0));
        assert!(approx_eq(result[1], 1.0));
    }

    #[test]
    fn transpose_is_inverse() {
        let r = Rotation2::new(Radians::new(PI / 4.0));
        let rt = r.transpose();
        let composed = r * rt;
        assert!(approx_eq(composed.as_matrix()[0][0], 1.0));
        assert!(approx_eq(composed.as_matrix()[0][1], 0.0));
        assert!(approx_eq(composed.as_matrix()[1][0], 0.0));
        assert!(approx_eq(composed.as_matrix()[1][1], 1.0));
    }

    #[test]
    fn inverse_undoes_rotation() {
        let r = Rotation2::new(Radians::new(FRAC_PI_2));
        let v = [1.0, 0.0];
        let rotated = r.apply_array(v);
        let back = r.inverse().apply_array(rotated);
        assert!(approx_eq_arr(back, v));
    }

    #[test]
    fn compose_adds_angles() {
        let r1 = Rotation2::new(Radians::new(FRAC_PI_2));
        let r2 = Rotation2::new(Radians::new(FRAC_PI_2));
        let combined = r1.compose(&r2);
        let result = combined.apply_array([1.0, 0.0]);
        // 180° rotation → [-1, 0]
        assert!(approx_eq(result[0], -1.0));
        assert!(approx_eq(result[1], 0.0));
    }

    #[test]
    fn mul_rotation_same_as_compose() {
        let r1 = Rotation2::new(Radians::new(1.0));
        let r2 = Rotation2::new(Radians::new(0.5));
        let via_mul = r1 * r2;
        let via_compose = r1.compose(&r2);
        assert_eq!(via_mul, via_compose);
    }

    #[test]
    fn mul_array_same_as_apply_array() {
        let r = Rotation2::new(Radians::new(0.7));
        let v = [3.0, 4.0];
        assert_eq!(r * v, r.apply_array(v));
    }

    #[test]
    fn apply_array_identity_is_noop() {
        let v = [5.0, -3.0];
        assert_eq!(Rotation2::IDENTITY.apply_array(v), v);
    }
}
