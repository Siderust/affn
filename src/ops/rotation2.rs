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
        let m = self.m.map(|row| {
            core::array::from_fn(|j| row[0] * rhs.m[0][j] + row[1] * rhs.m[1][j])
        });
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
