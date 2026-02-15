//! 3x3 rotation matrix operator.

use crate::cartesian::xyz::XYZ;
use qtty::Radians;

/// A 3x3 rotation matrix for orientation transforms.
///
/// Internally stores row-major data as `[[f64; 3]; 3]`.
/// This is a pure mathematical operator with no frame semantics—
/// frame tagging is handled by the caller.
///
/// # Conventions
///
/// - Right-handed coordinate system assumed.
/// - Matrix applied as `y = R * x` (column vector convention).
/// - Transpose of a rotation matrix is its inverse.
///
/// # Example
///
/// ```rust
/// use affn::Rotation3;
/// use qtty::Radians;
/// use std::f64::consts::FRAC_PI_2;
///
/// // Rotate 90° around the Z axis
/// let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
/// let x_axis = [1.0, 0.0, 0.0];
/// let rotated = rot.apply_array(x_axis);
///
/// // X-axis becomes Y-axis (within numerical tolerance)
/// assert!((rotated[0]).abs() < 1e-10);
/// assert!((rotated[1] - 1.0).abs() < 1e-10);
/// assert!((rotated[2]).abs() < 1e-10);
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Rotation3 {
    /// Row-major 3x3 rotation matrix.
    /// `m[row][col]`
    m: [[f64; 3]; 3],
}

impl Rotation3 {
    /// The identity rotation (no change in orientation).
    pub const IDENTITY: Self = Self {
        m: [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
    };

    /// Creates a rotation matrix from raw row-major data.
    ///
    /// # Arguments
    /// - `m`: A 3x3 array in row-major order where `m[row][col]`.
    ///
    /// # Safety
    /// The caller must ensure `m` is a valid rotation matrix (orthogonal, det = +1).
    /// No validation is performed.
    #[inline]
    pub const fn from_matrix(m: [[f64; 3]; 3]) -> Self {
        Self { m }
    }

    /// Creates a rotation from an axis-angle representation.
    ///
    /// Uses Rodrigues' rotation formula.
    ///
    /// # Arguments
    /// - `axis`: The rotation axis (will be normalized if not unit length).
    /// - `angle`: The rotation angle (right-hand rule).
    ///
    /// # Returns
    /// A rotation matrix representing the given axis-angle rotation.
    #[inline]
    pub fn from_axis_angle(axis: [f64; 3], angle: Radians) -> Self {
        let [x, y, z] = axis;
        let mag = (x * x + y * y + z * z).sqrt();
        if mag < f64::EPSILON {
            return Self::IDENTITY;
        }

        // Normalize axis
        let (x, y, z) = (x / mag, y / mag, z / mag);

        let (s, c) = angle.sin_cos();
        let t = 1.0 - c;

        Self {
            m: [
                [t * x * x + c, t * x * y - s * z, t * x * z + s * y],
                [t * x * y + s * z, t * y * y + c, t * y * z - s * x],
                [t * x * z - s * y, t * y * z + s * x, t * z * z + c],
            ],
        }
    }

    /// Creates a rotation around the X axis.
    ///
    /// # Arguments
    /// - `angle`: Rotation angle (right-hand rule around +X).
    #[inline]
    fn from_x_rotation(angle: f64) -> Self {
        let (s, c) = (angle.sin(), angle.cos());
        Self {
            m: [[1.0, 0.0, 0.0], [0.0, c, -s], [0.0, s, c]],
        }
    }

    /// Creates a rotation around the Y axis.
    ///
    /// # Arguments
    /// - `angle`: Rotation angle (right-hand rule around +Y).
    #[inline]
    fn from_y_rotation(angle: f64) -> Self {
        let (s, c) = (angle.sin(), angle.cos());
        Self {
            m: [[c, 0.0, s], [0.0, 1.0, 0.0], [-s, 0.0, c]],
        }
    }

    /// Creates a rotation around the Z axis.
    ///
    /// # Arguments
    /// - `angle`: Rotation angle (right-hand rule around +Z).
    #[inline]
    fn from_z_rotation(angle: f64) -> Self {
        let (s, c) = (angle.sin(), angle.cos());
        Self {
            m: [[c, -s, 0.0], [s, c, 0.0], [0.0, 0.0, 1.0]],
        }
    }

    /// Creates a rotation from Euler angles (XYZ convention).
    ///
    /// Applies rotations in order: X, then Y, then Z.
    ///
    /// # Arguments
    /// - `x`: Rotation around X axis.
    /// - `y`: Rotation around Y axis.
    /// - `z`: Rotation around Z axis.
    #[inline]
    pub fn from_euler_xyz(x: Radians, y: Radians, z: Radians) -> Self {
        Self::rz(z) * Self::ry(y) * Self::rx(x)
    }

    /// Creates a rotation from Euler angles (ZXZ convention).
    ///
    /// This is the classical astronomical convention used in precession.
    /// Applies rotations in order: first Z, then X, then Z.
    ///
    /// # Arguments
    /// - `z1`: First rotation around Z axis.
    /// - `x`: Rotation around X axis.
    /// - `z2`: Second rotation around Z axis.
    #[inline]
    pub fn from_euler_zxz(z1: Radians, x: Radians, z2: Radians) -> Self {
        Self::rz(z2) * Self::rx(x) * Self::rz(z1)
    }

    // ─── Typed-angle constructors (Radians from qtty) ───

    /// Creates a rotation around the X axis from a typed `Radians` angle.
    #[inline]
    pub fn rx(angle: Radians) -> Self {
        Self::from_x_rotation(angle.value())
    }

    /// Creates a rotation around the Y axis from a typed `Radians` angle.
    #[inline]
    pub fn ry(angle: Radians) -> Self {
        Self::from_y_rotation(angle.value())
    }

    /// Creates a rotation around the Z axis from a typed `Radians` angle.
    #[inline]
    pub fn rz(angle: Radians) -> Self {
        Self::from_z_rotation(angle.value())
    }

    /// Returns the transpose (inverse) of this rotation.
    ///
    /// For rotation matrices, transpose equals inverse.
    #[inline]
    pub fn transpose(&self) -> Self {
        Self {
            m: [
                [self.m[0][0], self.m[1][0], self.m[2][0]],
                [self.m[0][1], self.m[1][1], self.m[2][1]],
                [self.m[0][2], self.m[1][2], self.m[2][2]],
            ],
        }
    }

    /// Returns the inverse of this rotation.
    ///
    /// Alias for [`transpose`](Self::transpose).
    #[inline]
    pub fn inverse(&self) -> Self {
        self.transpose()
    }

    /// Composes two rotations: `self * other`.
    ///
    /// The result applies `other` first, then `self`.
    #[inline]
    pub fn compose(&self, other: &Self) -> Self {
        *self * *other
    }

    /// Applies this rotation to a raw `[f64; 3]` array.
    ///
    /// Computes `R * v` where `v` is treated as a column vector.
    #[inline]
    pub fn apply_array(&self, v: [f64; 3]) -> [f64; 3] {
        [
            self.m[0][0] * v[0] + self.m[0][1] * v[1] + self.m[0][2] * v[2],
            self.m[1][0] * v[0] + self.m[1][1] * v[1] + self.m[1][2] * v[2],
            self.m[2][0] * v[0] + self.m[2][1] * v[1] + self.m[2][2] * v[2],
        ]
    }

    /// Applies this rotation to an `XYZ<f64>`.
    #[inline]
    pub fn apply_xyz(&self, xyz: XYZ<f64>) -> XYZ<f64> {
        let [x, y, z] = self.apply_array([xyz.x(), xyz.y(), xyz.z()]);
        XYZ::new(x, y, z)
    }

    /// Returns the underlying matrix as a row-major array.
    #[inline]
    pub const fn as_matrix(&self) -> &[[f64; 3]; 3] {
        &self.m
    }
}

impl Default for Rotation3 {
    fn default() -> Self {
        Self::IDENTITY
    }
}

// Matrix multiplication for composing rotations
impl std::ops::Mul for Rotation3 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let mut m = [[0.0; 3]; 3];
        #[allow(clippy::needless_range_loop)]
        for i in 0..3 {
            for j in 0..3 {
                m[i][j] = self.m[i][0] * rhs.m[0][j]
                    + self.m[i][1] * rhs.m[1][j]
                    + self.m[i][2] * rhs.m[2][j];
            }
        }
        Self { m }
    }
}

/// Applies a rotation to a raw `[f64; 3]` column vector: `R * v`.
impl std::ops::Mul<[f64; 3]> for Rotation3 {
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
    use qtty::Radians;
    use std::f64::consts::{FRAC_PI_2, PI};

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
    fn test_rotation_identity() {
        let r = Rotation3::IDENTITY;
        let v = [1.0, 2.0, 3.0];
        assert_array_eq(r.apply_array(v), v, "Identity should not change vector");
    }

    #[test]
    fn test_rotation_z_90() {
        let r = Rotation3::rz(Radians::new(FRAC_PI_2));
        let x = [1.0, 0.0, 0.0];
        let result = r.apply_array(x);
        assert_array_eq(result, [0.0, 1.0, 0.0], "X-axis should rotate to Y-axis");
    }

    #[test]
    fn test_rotation_x_90() {
        let r = Rotation3::rx(Radians::new(FRAC_PI_2));
        let y = [0.0, 1.0, 0.0];
        let result = r.apply_array(y);
        assert_array_eq(result, [0.0, 0.0, 1.0], "Y-axis should rotate to Z-axis");
    }

    #[test]
    fn test_rotation_y_90() {
        let r = Rotation3::ry(Radians::new(FRAC_PI_2));
        let z = [0.0, 0.0, 1.0];
        let result = r.apply_array(z);
        assert_array_eq(result, [1.0, 0.0, 0.0], "Z-axis should rotate to X-axis");
    }

    #[test]
    fn test_rotation_axis_angle() {
        let r = Rotation3::from_axis_angle([0.0, 0.0, 1.0], Radians::new(PI));
        let x = [1.0, 0.0, 0.0];
        let result = r.apply_array(x);
        assert_array_eq(result, [-1.0, 0.0, 0.0], "180° around Z should flip X");
    }

    #[test]
    fn test_rotation_inverse() {
        let r = Rotation3::rz(Radians::new(0.7));
        let r_inv = r.inverse();
        let composed = r.compose(&r_inv);

        let v = [1.0, 2.0, 3.0];
        let result = composed.apply_array(v);
        assert_array_eq(result, v, "R * R^-1 should be identity");
    }

    #[test]
    fn test_rotation_composition() {
        let r90 = Rotation3::rz(Radians::new(FRAC_PI_2));
        let r180 = r90.compose(&r90);

        let x = [1.0, 0.0, 0.0];
        let result = r180.apply_array(x);
        assert_array_eq(result, [-1.0, 0.0, 0.0], "Two 90° rotations = 180°");
    }

    #[test]
    fn test_rotation_xyz_type() {
        let r = Rotation3::rz(Radians::new(FRAC_PI_2));
        let xyz = XYZ::new(1.0, 0.0, 0.0);
        let result = r.apply_xyz(xyz);
        assert!((result.x()).abs() < EPSILON);
        assert!((result.y() - 1.0).abs() < EPSILON);
        assert!((result.z()).abs() < EPSILON);
    }

    #[test]
    fn test_rotation_euler_and_matrix_helpers() {
        let v = [1.0, 2.0, 3.0];
        let r_xyz = Rotation3::from_euler_xyz(
            Radians::new(0.1),
            Radians::new(0.2),
            Radians::new(0.3),
        );
        let manual = Rotation3::rz(Radians::new(0.3))
            * Rotation3::ry(Radians::new(0.2))
            * Rotation3::rx(Radians::new(0.1));
        assert_array_eq(r_xyz.apply_array(v), manual.apply_array(v), "Euler XYZ");

        let r_zxz = Rotation3::from_euler_zxz(
            Radians::new(0.1),
            Radians::new(0.2),
            Radians::new(0.3),
        );
        let manual_zxz = Rotation3::rz(Radians::new(0.3))
            * Rotation3::rx(Radians::new(0.2))
            * Rotation3::rz(Radians::new(0.1));
        assert_array_eq(r_zxz.apply_array(v), manual_zxz.apply_array(v), "Euler ZXZ");

        let identity = Rotation3::default();
        assert_eq!(identity, Rotation3::IDENTITY);
        let matrix = *identity.as_matrix();
        let from_matrix = Rotation3::from_matrix(matrix);
        assert_eq!(from_matrix, Rotation3::IDENTITY);
    }

    #[test]
    fn test_rotation_mul_f64_array() {
        let r = Rotation3::rz(Radians::new(FRAC_PI_2));
        let result = r * [1.0, 0.0, 0.0];
        assert_array_eq(result, [0.0, 1.0, 0.0], "Rotation * [f64; 3]");
    }

    #[test]
    fn test_rotation_mul_quantity_array() {
        use qtty::Meter;
        use qtty::Quantity;
        let r = Rotation3::rz(Radians::new(FRAC_PI_2));
        let v = [
            Quantity::<Meter>::new(1.0),
            Quantity::<Meter>::new(0.0),
            Quantity::<Meter>::new(0.0),
        ];
        let result = r * v;
        assert!((result[0].value()).abs() < EPSILON);
        assert!((result[1].value() - 1.0).abs() < EPSILON);
        assert!((result[2].value()).abs() < EPSILON);
    }

    #[test]
    fn test_rotation_mul_xyz_quantity() {
        use qtty::Meter;
        use qtty::Quantity;
        let r = Rotation3::rz(Radians::new(FRAC_PI_2));
        let xyz: XYZ<Quantity<Meter>> = XYZ::new(
            Quantity::<Meter>::new(1.0),
            Quantity::<Meter>::new(0.0),
            Quantity::<Meter>::new(0.0),
        );
        let result = r * xyz;
        assert!((result.x().value()).abs() < EPSILON);
        assert!((result.y().value() - 1.0).abs() < EPSILON);
        assert!((result.z().value()).abs() < EPSILON);
    }

    #[test]
    fn test_rotation_mul_quantity_preserves_unit() {
        use qtty::{AstronomicalUnit, Quantity};
        let r = Rotation3::rz(Radians::new(FRAC_PI_2));
        let v = [
            Quantity::<AstronomicalUnit>::new(3.0),
            Quantity::<AstronomicalUnit>::new(0.0),
            Quantity::<AstronomicalUnit>::new(0.0),
        ];
        let result = r * v;
        assert!((result[0].value()).abs() < EPSILON);
        assert!((result[1].value() - 3.0).abs() < EPSILON);
        assert!((result[2].value()).abs() < EPSILON);
    }

    #[test]
    fn test_rotation_mul_quantity_roundtrip() {
        use qtty::{Meter, Quantity};
        let r = Rotation3::rz(Radians::new(0.7));
        let r_inv = r.inverse();
        let v = [
            Quantity::<Meter>::new(1.0),
            Quantity::<Meter>::new(2.0),
            Quantity::<Meter>::new(3.0),
        ];
        let result = r_inv * (r * v);
        assert!((result[0].value() - 1.0).abs() < EPSILON);
        assert!((result[1].value() - 2.0).abs() < EPSILON);
        assert!((result[2].value() - 3.0).abs() < EPSILON);
    }
}
