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
    /// Internally uses a fused constructor to avoid intermediate matrices.
    ///
    /// # Arguments
    /// - `x`: Rotation around X axis.
    /// - `y`: Rotation around Y axis.
    /// - `z`: Rotation around Z axis.
    #[inline]
    pub fn from_euler_xyz(x: Radians, y: Radians, z: Radians) -> Self {
        let (sx, cx) = x.sin_cos();
        let (sy, cy) = y.sin_cos();
        let (sz, cz) = z.sin_cos();

        // M = Rz(z) * Ry(y) * Rx(x) — fused
        let cz_sy = cz * sy;
        let sz_sy = sz * sy;
        Self {
            m: [
                [cz * cy, cz_sy * sx - sz * cx, cz_sy * cx + sz * sx],
                [sz * cy, sz_sy * sx + cz * cx, sz_sy * cx - cz * sx],
                [-sy, cy * sx, cy * cx],
            ],
        }
    }

    /// Creates a rotation from Euler angles (ZXZ convention).
    ///
    /// This is the classical astronomical convention used in precession.
    /// Applies rotations in order: first Z, then X, then Z.
    /// Internally uses a fused constructor to avoid intermediate matrices.
    ///
    /// # Arguments
    /// - `z1`: First rotation around Z axis.
    /// - `x`: Rotation around X axis.
    /// - `z2`: Second rotation around Z axis.
    #[inline]
    pub fn from_euler_zxz(z1: Radians, x: Radians, z2: Radians) -> Self {
        // Rz(z2) * Rx(x) * Rz(z1) has the same structure as Rz * Rx * Rz
        // which is the transpose pattern of fused_rx_rz_rx with swapped roles.
        // Compute directly:
        let (s1, c1) = z1.sin_cos();
        let (sx, cx) = x.sin_cos();
        let (s2, c2) = z2.sin_cos();

        let c2_cx = c2 * cx;
        let s2_cx = s2 * cx;
        Self {
            m: [
                [c2 * c1 - s2_cx * s1, -(c2 * s1 + s2_cx * c1), s2 * sx],
                [s2 * c1 + c2_cx * s1, -(s2 * s1) + c2_cx * c1, -c2 * sx],
                [sx * s1, sx * c1, cx],
            ],
        }
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

    // ─── Fused multi-rotation constructors ───
    //
    // These construct a rotation matrix from multiple angles in a single
    // step, computing the 9 matrix elements directly from trigonometric
    // products. This avoids constructing intermediate rotation matrices
    // and performing matrix multiplications.

    /// Constructs the rotation `Rx(a) · Rz(b)` directly.
    ///
    /// Faster than `Rotation3::rx(a) * Rotation3::rz(b)` because it avoids
    /// the intermediate 3×3 matrix multiply and computes each element
    /// from trig products.
    ///
    /// # Arguments
    /// - `a`: Angle for the X rotation (applied second / left factor).
    /// - `b`: Angle for the Z rotation (applied first / right factor).
    #[inline]
    pub fn fused_rx_rz(a: Radians, b: Radians) -> Self {
        let (sa, ca) = a.sin_cos();
        let (sb, cb) = b.sin_cos();
        Self {
            m: [
                [cb, -sb, 0.0],
                [ca * sb, ca * cb, -sa],
                [sa * sb, sa * cb, ca],
            ],
        }
    }

    /// Constructs the rotation `Rz(a) · Rx(b)` directly.
    ///
    /// Faster than `Rotation3::rz(a) * Rotation3::rx(b)` because it avoids
    /// the intermediate 3×3 matrix multiply.
    ///
    /// # Arguments
    /// - `a`: Angle for the Z rotation (applied second / left factor).
    /// - `b`: Angle for the X rotation (applied first / right factor).
    #[inline]
    pub fn fused_rz_rx(a: Radians, b: Radians) -> Self {
        let (sa, ca) = a.sin_cos();
        let (sb, cb) = b.sin_cos();
        Self {
            m: [
                [ca, -sa * cb, sa * sb],
                [sa, ca * cb, -ca * sb],
                [0.0, sb, cb],
            ],
        }
    }

    /// Constructs the rotation `Rx(a) · Rz(b) · Rx(c)` directly.
    ///
    /// Used in nutation: `N = Rx(ε+Δε) · Rz(Δψ) · Rx(−ε)`.
    ///
    /// Computes the 9 elements from 3 sin/cos pairs and their products,
    /// avoiding 2 intermediate matrix multiplications.
    ///
    /// # Arguments
    /// - `a`: Angle for the outer X rotation (left).
    /// - `b`: Angle for the Z rotation (middle).
    /// - `c`: Angle for the inner X rotation (right).
    #[inline]
    pub fn fused_rx_rz_rx(a: Radians, b: Radians, c: Radians) -> Self {
        let (sa, ca) = a.sin_cos();
        let (sb, cb) = b.sin_cos();
        let (sc, cc) = c.sin_cos();

        // M = Rx(a) * Rz(b) * Rx(c)
        // Row 0: [cb, -sb*cc, sb*sc]
        // Row 1: [ca*sb, ca*cb*cc - sa*sc, -ca*cb*sc - sa*cc]
        // Row 2: [sa*sb, sa*cb*cc + ca*sc, -sa*cb*sc + ca*cc]
        let ca_cb = ca * cb;
        let sa_cb = sa * cb;
        Self {
            m: [
                [cb, -sb * cc, sb * sc],
                [
                    ca * sb,
                    ca_cb * cc - sa * sc,
                    -(ca_cb * sc + sa * cc),
                ],
                [
                    sa * sb,
                    sa_cb * cc + ca * sc,
                    -(sa_cb * sc) + ca * cc,
                ],
            ],
        }
    }

    /// Constructs the rotation `Rz(a) · Ry(b) · Rz(c)` directly.
    ///
    /// Used in Meeus precession: `P = Rz(z) · Ry(−θ) · Rz(ζ)`.
    ///
    /// # Arguments
    /// - `a`: Angle for the outer Z rotation (left).
    /// - `b`: Angle for the Y rotation (middle).
    /// - `c`: Angle for the inner Z rotation (right).
    #[inline]
    pub fn fused_rz_ry_rz(a: Radians, b: Radians, c: Radians) -> Self {
        let (sa, ca) = a.sin_cos();
        let (sb, cb) = b.sin_cos();
        let (sc, cc) = c.sin_cos();

        // M = Rz(a) * Ry(b) * Rz(c)
        let ca_cb = ca * cb;
        let sa_cb = sa * cb;
        Self {
            m: [
                [
                    ca_cb * cc - sa * sc,
                    -(ca_cb * sc + sa * cc),
                    ca * sb,
                ],
                [
                    sa_cb * cc + ca * sc,
                    -(sa_cb * sc) + ca * cc,
                    sa * sb,
                ],
                [-sb * cc, sb * sc, cb],
            ],
        }
    }

    /// Constructs the Fukushima-Williams rotation `Rx(a) · Rz(b) · Rx(c) · Rz(d)` directly.
    ///
    /// This is the standard form for IAU 2006 precession and precession-nutation
    /// matrices. In the SOFA/ERFA convention (translated to standard rotations):
    ///
    /// ```text
    /// P = Rx(ε_A) · Rz(ψ̄) · Rx(−φ̄) · Rz(−γ̄)
    /// ```
    ///
    /// This fused constructor computes all 9 matrix elements directly from
    /// 4 sin/cos pairs, avoiding 3 intermediate matrix multiplications.
    /// Provides a ~45% speedup over the sequential composition.
    ///
    /// # Arguments
    /// - `a`: Angle for the outer X rotation (left, e.g., ε_A).
    /// - `b`: Angle for the first Z rotation (e.g., ψ̄).
    /// - `c`: Angle for the inner X rotation (e.g., −φ̄).
    /// - `d`: Angle for the innermost Z rotation (e.g., −γ̄).
    #[inline]
    pub fn fused_rx_rz_rx_rz(a: Radians, b: Radians, c: Radians, d: Radians) -> Self {
        let (sa, ca) = a.sin_cos();
        let (sb, cb) = b.sin_cos();
        let (sc, cc) = c.sin_cos();
        let (sd, cd) = d.sin_cos();

        // M = Rx(a) * Rz(b) * Rx(c) * Rz(d)
        //
        // Let P = Rx(a) * Rz(b) * Rx(c)  (the 3-rotation from fused_rx_rz_rx)
        // Then M = P * Rz(d)
        //
        // P = [[cb,        -sb*cc,          sb*sc      ],
        //      [ca*sb,      ca*cb*cc-sa*sc, -ca*cb*sc-sa*cc],
        //      [sa*sb,      sa*cb*cc+ca*sc, -sa*cb*sc+ca*cc]]
        //
        // Rz(d) = [[cd, -sd, 0],
        //          [sd,  cd, 0],
        //          [0,   0,  1]]
        //
        // M[i][0] = P[i][0]*cd + P[i][1]*sd
        // M[i][1] = -P[i][0]*sd + P[i][1]*cd
        // M[i][2] = P[i][2]

        // Precompute P columns 0 and 1
        let ca_cb = ca * cb;
        let sa_cb = sa * cb;
        let sb_cc = sb * cc;
        let sb_sc = sb * sc;

        let p00 = cb;
        let p01 = -sb_cc;
        let p10 = ca * sb;
        let p11 = ca_cb * cc - sa * sc;
        let p20 = sa * sb;
        let p21 = sa_cb * cc + ca * sc;

        Self {
            m: [
                [
                    p00 * cd + p01 * sd,
                    -p00 * sd + p01 * cd,
                    sb_sc,
                ],
                [
                    p10 * cd + p11 * sd,
                    -p10 * sd + p11 * cd,
                    -(ca_cb * sc + sa * cc),
                ],
                [
                    p20 * cd + p21 * sd,
                    -p20 * sd + p21 * cd,
                    -(sa_cb * sc) + ca * cc,
                ],
            ],
        }
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
        let r_xyz =
            Rotation3::from_euler_xyz(Radians::new(0.1), Radians::new(0.2), Radians::new(0.3));
        let manual = Rotation3::rz(Radians::new(0.3))
            * Rotation3::ry(Radians::new(0.2))
            * Rotation3::rx(Radians::new(0.1));
        assert_array_eq(r_xyz.apply_array(v), manual.apply_array(v), "Euler XYZ");

        let r_zxz =
            Rotation3::from_euler_zxz(Radians::new(0.1), Radians::new(0.2), Radians::new(0.3));
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

    // =========================================================================
    // Fused constructor correctness tests
    // =========================================================================

    fn assert_matrix_eq(a: &Rotation3, b: &Rotation3, msg: &str) {
        let ma = a.as_matrix();
        let mb = b.as_matrix();
        for i in 0..3 {
            for j in 0..3 {
                assert!(
                    (ma[i][j] - mb[i][j]).abs() < EPSILON,
                    "{}: element [{i}][{j}] differs: {} vs {}",
                    msg,
                    ma[i][j],
                    mb[i][j]
                );
            }
        }
    }

    #[test]
    fn test_fused_rx_rz() {
        let a = Radians::new(0.409_092_804);
        let b = Radians::new(0.001_234_567);
        let naive = Rotation3::rx(a) * Rotation3::rz(b);
        let fused = Rotation3::fused_rx_rz(a, b);
        assert_matrix_eq(&naive, &fused, "fused_rx_rz");
    }

    #[test]
    fn test_fused_rz_rx() {
        let a = Radians::new(1.234_567_890);
        let b = Radians::new(-0.123_456_789);
        let naive = Rotation3::rz(a) * Rotation3::rx(b);
        let fused = Rotation3::fused_rz_rx(a, b);
        assert_matrix_eq(&naive, &fused, "fused_rz_rx");
    }

    #[test]
    fn test_fused_rx_rz_rx() {
        let a = Radians::new(0.409_092_804);
        let b = Radians::new(0.001_234_567);
        let c = Radians::new(-0.409_000_000);
        let naive = Rotation3::rx(a) * Rotation3::rz(b) * Rotation3::rx(c);
        let fused = Rotation3::fused_rx_rz_rx(a, b, c);
        assert_matrix_eq(&naive, &fused, "fused_rx_rz_rx");
    }

    #[test]
    fn test_fused_rz_ry_rz() {
        let a = Radians::new(0.409_092_804);
        let b = Radians::new(-0.001_234_567);
        let c = Radians::new(0.000_012_345);
        let naive = Rotation3::rz(a) * Rotation3::ry(b) * Rotation3::rz(c);
        let fused = Rotation3::fused_rz_ry_rz(a, b, c);
        assert_matrix_eq(&naive, &fused, "fused_rz_ry_rz");
    }

    #[test]
    fn test_fused_rx_rz_rx_rz() {
        // Fukushima-Williams angles
        let epsa = Radians::new(0.409_092_804);
        let psib = Radians::new(0.001_234_567);
        let phib = Radians::new(-0.409_000_000);
        let gamb = Radians::new(-1.234_567_890);
        let naive = Rotation3::rx(epsa) * Rotation3::rz(psib) * Rotation3::rx(phib) * Rotation3::rz(gamb);
        let fused = Rotation3::fused_rx_rz_rx_rz(epsa, psib, phib, gamb);
        assert_matrix_eq(&naive, &fused, "fused_rx_rz_rx_rz");
    }

    #[test]
    fn test_fused_fw_precession_equivalent() {
        // Simulate the exact Fukushima-Williams call pattern:
        // fw_matrix(gamb, phib, psib, epsa) = Rx(epsa) * Rz(psib) * Rx(-phib) * Rz(-gamb)
        let gamb = Radians::new(0.000_001_234);
        let phib = Radians::new(0.409_350_000);
        let psib = Radians::new(0.024_500_000);
        let epsa = Radians::new(0.409_092_804);
        let naive = Rotation3::rx(epsa) * Rotation3::rz(psib) * Rotation3::rx(-phib) * Rotation3::rz(-gamb);
        let fused = Rotation3::fused_rx_rz_rx_rz(epsa, psib, -phib, -gamb);
        assert_matrix_eq(&naive, &fused, "FW precession");
    }

    #[test]
    fn test_fused_nutation_equivalent() {
        // Nutation: Rx(eps+deps) * Rz(dpsi) * Rx(-eps)
        let eps = Radians::new(0.409_092_804);
        let dpsi = Radians::new(0.000_012_345);
        let deps = Radians::new(-0.000_006_789);
        let naive = Rotation3::rx(eps + deps) * Rotation3::rz(dpsi) * Rotation3::rx(-eps);
        let fused = Rotation3::fused_rx_rz_rx(eps + deps, dpsi, -eps);
        assert_matrix_eq(&naive, &fused, "nutation");
    }

    #[test]
    fn test_fused_vectors_match() {
        // Verify that fused rotations rotate vectors identically
        let v = [0.123_456_789, 0.987_654_321, 0.456_789_012];
        let a = Radians::new(0.409_092_804);
        let b = Radians::new(0.001_234_567);
        let c = Radians::new(-0.409_000_000);
        let d = Radians::new(-1.234_567_890);

        let naive = Rotation3::rx(a) * Rotation3::rz(b) * Rotation3::rx(c) * Rotation3::rz(d);
        let fused = Rotation3::fused_rx_rz_rx_rz(a, b, c, d);

        let v_naive = naive.apply_array(v);
        let v_fused = fused.apply_array(v);
        assert_array_eq(v_naive, v_fused, "fused FW rotation vector result");
    }
}
