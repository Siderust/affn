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
//! ## Application Semantics
//!
//! | Operator       | Applies To      | Result Type             |
//! |----------------|-----------------|-------------------------|
//! | `Rotation3`    | `Direction<F>`  | `Direction<F2>`         |
//! | `Rotation3`    | `Vector<F,U>`   | `Vector<F2,U>`          |
//! | `Rotation3`    | `Position<C,F,U>` | `Position<C,F2,U>`    |
//! | `Translation3` | `Position<C,F,U>` | `Position<C2,F,U>`    |
//! | `Isometry3`    | `Position<C,F,U>` | `Position<C2,F2,U>`   |
//!
//! **Note**: Translations do not apply to `Direction` or `Vector` since these are
//! translation-invariant (free vectors).

use crate::cartesian::xyz::XYZ;

// =============================================================================
// Rotation3: 3x3 Rotation Matrix
// =============================================================================

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
/// use std::f64::consts::FRAC_PI_2;
///
/// // Rotate 90° around the Z axis
/// let rot = Rotation3::from_axis_angle([0.0, 0.0, 1.0], FRAC_PI_2);
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
    /// - `angle`: The rotation angle in radians (right-hand rule).
    ///
    /// # Returns
    /// A rotation matrix representing the given axis-angle rotation.
    #[inline]
    pub fn from_axis_angle(axis: [f64; 3], angle: f64) -> Self {
        let [x, y, z] = axis;
        let mag = (x * x + y * y + z * z).sqrt();
        if mag < f64::EPSILON {
            return Self::IDENTITY;
        }

        // Normalize axis
        let (x, y, z) = (x / mag, y / mag, z / mag);

        let (s, c) = (angle.sin(), angle.cos());
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
    /// - `angle`: Rotation angle in radians (right-hand rule around +X).
    #[inline]
    pub fn from_x_rotation(angle: f64) -> Self {
        let (s, c) = (angle.sin(), angle.cos());
        Self {
            m: [[1.0, 0.0, 0.0], [0.0, c, -s], [0.0, s, c]],
        }
    }

    /// Creates a rotation around the Y axis.
    ///
    /// # Arguments
    /// - `angle`: Rotation angle in radians (right-hand rule around +Y).
    #[inline]
    pub fn from_y_rotation(angle: f64) -> Self {
        let (s, c) = (angle.sin(), angle.cos());
        Self {
            m: [[c, 0.0, s], [0.0, 1.0, 0.0], [-s, 0.0, c]],
        }
    }

    /// Creates a rotation around the Z axis.
    ///
    /// # Arguments
    /// - `angle`: Rotation angle in radians (right-hand rule around +Z).
    #[inline]
    pub fn from_z_rotation(angle: f64) -> Self {
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
    /// - `x`: Rotation around X axis in radians.
    /// - `y`: Rotation around Y axis in radians.
    /// - `z`: Rotation around Z axis in radians.
    #[inline]
    pub fn from_euler_xyz(x: f64, y: f64, z: f64) -> Self {
        Self::from_z_rotation(z) * Self::from_y_rotation(y) * Self::from_x_rotation(x)
    }

    /// Creates a rotation from Euler angles (ZXZ convention).
    ///
    /// This is the classical astronomical convention used in precession.
    /// Applies rotations in order: first Z, then X, then Z.
    ///
    /// # Arguments
    /// - `z1`: First rotation around Z axis in radians.
    /// - `x`: Rotation around X axis in radians.
    /// - `z2`: Second rotation around Z axis in radians.
    #[inline]
    pub fn from_euler_zxz(z1: f64, x: f64, z2: f64) -> Self {
        Self::from_z_rotation(z2) * Self::from_x_rotation(x) * Self::from_z_rotation(z1)
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

// =============================================================================
// Translation3: Translation Vector
// =============================================================================

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

// =============================================================================
// Isometry3: Rotation + Translation
// =============================================================================

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

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
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

    // -------------------------------------------------------------------------
    // Rotation3 Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_rotation_identity() {
        let r = Rotation3::IDENTITY;
        let v = [1.0, 2.0, 3.0];
        assert_array_eq(r.apply_array(v), v, "Identity should not change vector");
    }

    #[test]
    fn test_rotation_z_90() {
        let r = Rotation3::from_z_rotation(FRAC_PI_2);
        let x = [1.0, 0.0, 0.0];
        let result = r.apply_array(x);
        assert_array_eq(result, [0.0, 1.0, 0.0], "X-axis should rotate to Y-axis");
    }

    #[test]
    fn test_rotation_x_90() {
        let r = Rotation3::from_x_rotation(FRAC_PI_2);
        let y = [0.0, 1.0, 0.0];
        let result = r.apply_array(y);
        assert_array_eq(result, [0.0, 0.0, 1.0], "Y-axis should rotate to Z-axis");
    }

    #[test]
    fn test_rotation_y_90() {
        let r = Rotation3::from_y_rotation(FRAC_PI_2);
        let z = [0.0, 0.0, 1.0];
        let result = r.apply_array(z);
        assert_array_eq(result, [1.0, 0.0, 0.0], "Z-axis should rotate to X-axis");
    }

    #[test]
    fn test_rotation_axis_angle() {
        // Rotate around Z-axis by 180 degrees
        let r = Rotation3::from_axis_angle([0.0, 0.0, 1.0], PI);
        let x = [1.0, 0.0, 0.0];
        let result = r.apply_array(x);
        assert_array_eq(result, [-1.0, 0.0, 0.0], "180° around Z should flip X");
    }

    #[test]
    fn test_rotation_inverse() {
        let r = Rotation3::from_z_rotation(0.7);
        let r_inv = r.inverse();
        let composed = r.compose(&r_inv);

        let v = [1.0, 2.0, 3.0];
        let result = composed.apply_array(v);
        assert_array_eq(result, v, "R * R^-1 should be identity");
    }

    #[test]
    fn test_rotation_composition() {
        // Two 90° rotations around Z should equal 180°
        let r90 = Rotation3::from_z_rotation(FRAC_PI_2);
        let r180 = r90.compose(&r90);

        let x = [1.0, 0.0, 0.0];
        let result = r180.apply_array(x);
        assert_array_eq(result, [-1.0, 0.0, 0.0], "Two 90° rotations = 180°");
    }

    #[test]
    fn test_rotation_xyz_type() {
        let r = Rotation3::from_z_rotation(FRAC_PI_2);
        let xyz = XYZ::new(1.0, 0.0, 0.0);
        let result = r.apply_xyz(xyz);
        assert!((result.x()).abs() < EPSILON);
        assert!((result.y() - 1.0).abs() < EPSILON);
        assert!((result.z()).abs() < EPSILON);
    }

    // -------------------------------------------------------------------------
    // Translation3 Tests
    // -------------------------------------------------------------------------

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

    // -------------------------------------------------------------------------
    // Isometry3 Tests
    // -------------------------------------------------------------------------

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
        let rot = Rotation3::from_z_rotation(FRAC_PI_2);
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
        // Rotate 90° around Z, then translate by (1, 0, 0)
        let rot = Rotation3::from_z_rotation(FRAC_PI_2);
        let trans = Translation3::new(1.0, 0.0, 0.0);
        let iso = Isometry3::new(rot, trans);

        // Point (1, 0, 0) -> rotate to (0, 1, 0) -> translate to (1, 1, 0)
        let p = [1.0, 0.0, 0.0];
        let result = iso.apply_point(p);
        assert_array_eq(result, [1.0, 1.0, 0.0], "Combined isometry");
    }

    #[test]
    fn test_isometry_inverse() {
        let rot = Rotation3::from_z_rotation(0.5);
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
            Rotation3::from_z_rotation(FRAC_PI_2),
            Translation3::new(1.0, 0.0, 0.0),
        );
        let iso2 = Isometry3::new(
            Rotation3::from_x_rotation(FRAC_PI_2),
            Translation3::new(0.0, 1.0, 0.0),
        );

        let composed = iso1.compose(&iso2);
        let p = [0.0, 0.0, 0.0];

        // Apply iso2 first: rotate Y->Z, translate (0,1,0) -> (0,1,0)
        // Apply iso1: rotate X->Y, translate (1,0,0)
        // iso2 on origin: (0,0,0) + (0,1,0) = (0,1,0)
        // iso1 on (0,1,0): rotate to (−1,0,0), then translate to (0,0,0)
        // Wait, let me recalculate...
        // iso2: R_x(90°) * (0,0,0) + (0,1,0) = (0,1,0)
        // iso1: R_z(90°) * (0,1,0) + (1,0,0) = (-1,0,0) + (1,0,0) = (0,0,0)

        let result = composed.apply_point(p);
        assert_array_eq(result, [0.0, 0.0, 0.0], "Composed isometry");
    }

    #[test]
    fn test_isometry_apply_vector() {
        let rot = Rotation3::from_z_rotation(FRAC_PI_2);
        let trans = Translation3::new(100.0, 200.0, 300.0);
        let iso = Isometry3::new(rot, trans);

        // Vectors should only be rotated, not translated
        let v = [1.0, 0.0, 0.0];
        let result = iso.apply_vector(v);
        assert_array_eq(result, [0.0, 1.0, 0.0], "Vector ignores translation");
    }
}
