// SPDX-License-Identifier: AGPL-3.0-only
// Copyright (C) 2026 Vallés Puig, Ramon

//! Frame-tagged 3×3 matrix primitives for affine geometry.
//!
//! This module provides two allocation-free, zero-cost frame-tagged 3×3 matrix
//! types generic over their element type:
//!
//! - [`FrameMatrix3<F, T>`] — a general 3×3 matrix in frame `F` with elements of
//!   type `T`. Supports constructors, transpose, frame relabelling, and (for
//!   `T = f64`) rotation-based similarity transforms.
//! - [`SymmetricFrameMatrix3<F, T>`] — same, but the matrix is guaranteed to be
//!   symmetric by construction. Suitable for covariance blocks and other bilinear
//!   forms.
//!
//! The frame tag `F` is a zero-sized phantom type that prevents mixing matrices
//! expressed in different frames at compile time.
//!
//! The element type `T` is `f64` by default, but any `Copy + Default` type is
//! accepted, enabling use with typed quantities from downstream crates.
//!
//! ## Rotation similarity
//!
//! Both types expose a `rotated_by::<G>(&r)` method (for `T = f64`) that
//! computes `R · M · Rᵀ` and relabels the result into frame `G`. For
//! [`SymmetricFrameMatrix3`] the result is numerically symmetrised to prevent
//! floating-point drift.
//!
//! ## Example
//!
//! ```rust
//! use affn::matrix3::{FrameMatrix3, SymmetricFrameMatrix3};
//! use affn::Rotation3;
//!
//! #[derive(Debug, Copy, Clone)]
//! struct BodyFrame;
//! impl affn::frames::ReferenceFrame for BodyFrame {
//!     fn frame_name() -> &'static str { "BodyFrame" }
//! }
//!
//! #[derive(Debug, Copy, Clone)]
//! struct WorldFrame;
//! impl affn::frames::ReferenceFrame for WorldFrame {
//!     fn frame_name() -> &'static str { "WorldFrame" }
//! }
//!
//! // Build a symmetric 3×3 diagonal matrix in BodyFrame.
//! let cov = SymmetricFrameMatrix3::<BodyFrame>::from_diagonal([1.0, 4.0, 9.0]);
//! assert_eq!(cov.diagonal(), [1.0, 4.0, 9.0]);
//!
//! // Rotate into WorldFrame with the identity rotation (no change in values).
//! let rotated = cov.rotated_by::<WorldFrame>(&Rotation3::IDENTITY);
//! assert!((rotated.as_array()[0][0] - 1.0).abs() < 1e-14);
//! assert!((rotated.as_array()[1][1] - 4.0).abs() < 1e-14);
//! assert!((rotated.as_array()[2][2] - 9.0).abs() < 1e-14);
//! ```

use core::marker::PhantomData;

use crate::ops::Rotation3;

// =============================================================================
// FrameMatrix3
// =============================================================================

/// Frame-tagged 3×3 matrix with element type `T` (default `f64`).
///
/// The phantom parameter `F` is the reference frame the matrix is expressed
/// in. The element type `T` defaults to `f64` but may be any `Copy + Default`
/// type, allowing matrices whose elements are typed quantities.
///
/// Symmetry is *not* enforced. Use [`SymmetricFrameMatrix3`] for covariance
/// blocks and other quantities that must remain symmetric.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FrameMatrix3<F, T = f64> {
    data: [[T; 3]; 3],
    _frame: PhantomData<F>,
}

impl<F, T: Copy + Default> FrameMatrix3<F, T> {
    /// Wrap a raw row-major 3×3 array as a matrix in frame `F`.
    #[inline]
    pub fn from_array(data: [[T; 3]; 3]) -> Self {
        Self { data, _frame: PhantomData }
    }

    /// Zero matrix in frame `F`.
    #[inline]
    pub fn zero() -> Self {
        Self::from_array([[T::default(); 3]; 3])
    }

    /// Borrow the underlying row-major 3×3 array.
    #[inline]
    pub fn as_array(&self) -> &[[T; 3]; 3] {
        &self.data
    }

    /// Transpose of this matrix.
    pub fn transpose(&self) -> Self {
        let mut out = [[T::default(); 3]; 3];
        for i in 0..3 {
            for j in 0..3 {
                out[i][j] = self.data[j][i];
            }
        }
        Self::from_array(out)
    }

    /// Re-tag the matrix as belonging to frame `G`, without changing data.
    ///
    /// Use this only when the data is already expressed in `G` by some other
    /// means; the type system cannot verify this.
    #[inline]
    pub fn relabel<G>(self) -> FrameMatrix3<G, T> {
        FrameMatrix3 { data: self.data, _frame: PhantomData }
    }
}

impl<F> FrameMatrix3<F> {
    /// 3×3 identity matrix in frame `F`.
    pub fn identity() -> Self {
        let mut d = [[0.0_f64; 3]; 3];
        for i in 0..3 {
            d[i][i] = 1.0;
        }
        Self::from_array(d)
    }

    /// Compute the similarity transform `R · self · Rᵀ`, tagging the result
    /// as belonging to frame `G`.
    ///
    /// This is the standard congruence transform for rotating a matrix into a
    /// new frame using the rotation `R : F → G`. For covariance-like uses,
    /// prefer [`SymmetricFrameMatrix3::rotated_by`] which also numerically
    /// re-symmetrises the result.
    pub fn rotated_by<G>(&self, r: &Rotation3) -> FrameMatrix3<G> {
        let rm = r.as_matrix();
        // tmp = R · self
        let mut tmp = [[0.0_f64; 3]; 3];
        for i in 0..3 {
            for k in 0..3 {
                let rik = rm[i][k];
                if rik == 0.0 {
                    continue;
                }
                for j in 0..3 {
                    tmp[i][j] += rik * self.data[k][j];
                }
            }
        }
        // result = tmp · Rᵀ  (Rᵀ[k][j] = R[j][k])
        let mut res = [[0.0_f64; 3]; 3];
        for i in 0..3 {
            for k in 0..3 {
                let tik = tmp[i][k];
                if tik == 0.0 {
                    continue;
                }
                for j in 0..3 {
                    res[i][j] += tik * rm[j][k];
                }
            }
        }
        FrameMatrix3::from_array(res)
    }
}

// =============================================================================
// SymmetricFrameMatrix3
// =============================================================================

/// Symmetric frame-tagged 3×3 matrix with element type `T` (default `f64`).
///
/// Symmetry (`data[i][j] == data[j][i]`) is guaranteed by all constructors.
/// The full 3×3 array is stored so element access is unconditional.
///
/// Typical uses: position–position, velocity–velocity covariance blocks, and
/// other bilinear forms that must remain symmetric under the operations applied
/// to them.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SymmetricFrameMatrix3<F, T = f64> {
    // Invariant: data[i][j] == data[j][i] for all i, j.
    data: [[T; 3]; 3],
    _frame: PhantomData<F>,
}

impl<F, T: Copy + Default> SymmetricFrameMatrix3<F, T> {
    /// Diagonal matrix with the given elements on the diagonal and zeros
    /// everywhere else.
    pub fn from_diagonal(diag: [T; 3]) -> Self {
        let mut data = [[T::default(); 3]; 3];
        for i in 0..3 {
            data[i][i] = diag[i];
        }
        Self { data, _frame: PhantomData }
    }

    /// Construct from the upper triangle (rows ≤ cols, including diagonal).
    ///
    /// Values at `upper[i][j]` for `i > j` (lower triangle) are ignored; the
    /// lower triangle is set to the mirror of the upper: `data[j][i] = upper[i][j]`.
    pub fn from_upper(upper: [[T; 3]; 3]) -> Self {
        let mut out = [[T::default(); 3]; 3];
        for i in 0..3 {
            for j in i..3 {
                out[i][j] = upper[i][j];
                out[j][i] = upper[i][j];
            }
        }
        Self { data: out, _frame: PhantomData }
    }

    /// Borrow the underlying row-major 3×3 array.
    #[inline]
    pub fn as_array(&self) -> &[[T; 3]; 3] {
        &self.data
    }

    /// Return the diagonal elements `[data[0][0], data[1][1], data[2][2]]`.
    #[inline]
    pub fn diagonal(&self) -> [T; 3] {
        [self.data[0][0], self.data[1][1], self.data[2][2]]
    }

    /// Transpose of a symmetric matrix is the matrix itself.
    #[inline]
    pub fn transpose(&self) -> Self {
        Self { data: self.data, _frame: PhantomData }
    }

    /// Re-tag the matrix as belonging to frame `G`, without changing data.
    #[inline]
    pub fn relabel<G>(self) -> SymmetricFrameMatrix3<G, T> {
        SymmetricFrameMatrix3 { data: self.data, _frame: PhantomData }
    }
}

impl<F> SymmetricFrameMatrix3<F> {
    /// 3×3 identity matrix in frame `F`.
    pub fn identity() -> Self {
        Self::from_diagonal([1.0, 1.0, 1.0])
    }

    /// Compute `R · self · Rᵀ`, tagging the result as belonging to frame `G`.
    ///
    /// For a rotation `R` and symmetric `self`, the result `R·M·Rᵀ` is
    /// algebraically symmetric. A final symmetrisation step averages
    /// `(result[i][j] + result[j][i]) / 2` to prevent floating-point drift
    /// from accumulating asymmetry over repeated transforms.
    pub fn rotated_by<G>(&self, r: &Rotation3) -> SymmetricFrameMatrix3<G> {
        let rm = r.as_matrix();
        // tmp = R · self
        let mut tmp = [[0.0_f64; 3]; 3];
        for i in 0..3 {
            for k in 0..3 {
                let rik = rm[i][k];
                if rik == 0.0 {
                    continue;
                }
                for j in 0..3 {
                    tmp[i][j] += rik * self.data[k][j];
                }
            }
        }
        // raw = tmp · Rᵀ
        let mut raw = [[0.0_f64; 3]; 3];
        for i in 0..3 {
            for k in 0..3 {
                let tik = tmp[i][k];
                if tik == 0.0 {
                    continue;
                }
                for j in 0..3 {
                    raw[i][j] += tik * rm[j][k];
                }
            }
        }
        // Symmetrize to guard against floating-point drift.
        let mut data = [[0.0_f64; 3]; 3];
        for i in 0..3 {
            for j in 0..3 {
                data[i][j] = 0.5 * (raw[i][j] + raw[j][i]);
            }
        }
        SymmetricFrameMatrix3 { data, _frame: PhantomData }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Copy, Clone)]
    struct F1;
    impl crate::frames::ReferenceFrame for F1 {
        fn frame_name() -> &'static str { "F1" }
    }

    #[derive(Debug, Copy, Clone)]
    struct F2;
    impl crate::frames::ReferenceFrame for F2 {
        fn frame_name() -> &'static str { "F2" }
    }

    // -------------------------------------------------------------------------
    // FrameMatrix3
    // -------------------------------------------------------------------------

    #[test]
    fn frame_matrix3_round_trip() {
        let data = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
        let m = FrameMatrix3::<F1>::from_array(data);
        assert_eq!(m.as_array(), &data);
    }

    #[test]
    fn frame_matrix3_zero() {
        let m = FrameMatrix3::<F1>::zero();
        for row in m.as_array() {
            for v in row {
                assert_eq!(*v, 0.0);
            }
        }
    }

    #[test]
    fn frame_matrix3_identity() {
        let m = FrameMatrix3::<F1>::identity();
        for i in 0..3 {
            for j in 0..3 {
                let expected = if i == j { 1.0 } else { 0.0 };
                assert_eq!(m.as_array()[i][j], expected);
            }
        }
    }

    #[test]
    fn frame_matrix3_transpose() {
        let data = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
        let m = FrameMatrix3::<F1>::from_array(data);
        let t = m.transpose();
        for i in 0..3 {
            for j in 0..3 {
                assert_eq!(t.as_array()[i][j], data[j][i]);
            }
        }
    }

    #[test]
    fn frame_matrix3_relabel() {
        let data = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
        let m1 = FrameMatrix3::<F1>::from_array(data);
        let m2: FrameMatrix3<F2> = m1.relabel();
        assert_eq!(m2.as_array(), &data);
    }

    #[test]
    fn frame_matrix3_rotated_by_identity_is_noop() {
        let data = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
        let m = FrameMatrix3::<F1>::from_array(data);
        let rotated: FrameMatrix3<F2> = m.rotated_by(&Rotation3::IDENTITY);
        for i in 0..3 {
            for j in 0..3 {
                assert!((rotated.as_array()[i][j] - data[i][j]).abs() < 1e-14);
            }
        }
    }

    /// Compile-time check: FrameMatrix3 accepts any Copy + Default element type.
    #[test]
    fn frame_matrix3_generic_element_type() {
        // i32
        let m = FrameMatrix3::<F1, i32>::from_array([[1, 0, 0], [0, 1, 0], [0, 0, 1]]);
        assert_eq!(m.as_array()[1][1], 1_i32);
        assert_eq!(m.transpose().as_array()[0][0], 1_i32);

        // u8
        let z = FrameMatrix3::<F1, u8>::zero();
        assert_eq!(z.as_array()[2][2], 0_u8);
    }

    // -------------------------------------------------------------------------
    // SymmetricFrameMatrix3
    // -------------------------------------------------------------------------

    #[test]
    fn symmetric_from_diagonal_round_trip() {
        let m = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 2.0, 3.0]);
        assert_eq!(m.diagonal(), [1.0, 2.0, 3.0]);
        // Off-diagonal must be zero.
        for i in 0..3 {
            for j in 0..3 {
                if i != j {
                    assert_eq!(m.as_array()[i][j], 0.0);
                }
            }
        }
    }

    #[test]
    fn symmetric_from_upper_mirrors_correctly() {
        // Upper triangle (i <= j):  (0,0)=1, (0,1)=2, (0,2)=3, (1,1)=4, (1,2)=5, (2,2)=6.
        let upper = [[1.0, 2.0, 3.0], [99.0, 4.0, 5.0], [99.0, 99.0, 6.0]];
        let m = SymmetricFrameMatrix3::<F1>::from_upper(upper);
        let a = m.as_array();
        // Diagonal
        assert_eq!(a[0][0], 1.0);
        assert_eq!(a[1][1], 4.0);
        assert_eq!(a[2][2], 6.0);
        // Upper = lower
        assert_eq!(a[0][1], 2.0);
        assert_eq!(a[1][0], 2.0);
        assert_eq!(a[0][2], 3.0);
        assert_eq!(a[2][0], 3.0);
        assert_eq!(a[1][2], 5.0);
        assert_eq!(a[2][1], 5.0);
    }

    #[test]
    fn symmetric_transpose_is_self() {
        let m = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 2.0, 3.0]);
        assert_eq!(m.transpose().as_array(), m.as_array());
    }

    #[test]
    fn symmetric_relabel() {
        let m1 = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 2.0, 3.0]);
        let m2: SymmetricFrameMatrix3<F2> = m1.relabel();
        assert_eq!(m2.diagonal(), [1.0, 2.0, 3.0]);
    }

    #[test]
    fn symmetric_rotated_by_identity_is_noop() {
        let m = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 4.0, 9.0]);
        let rotated: SymmetricFrameMatrix3<F2> = m.rotated_by(&Rotation3::IDENTITY);
        assert!((rotated.as_array()[0][0] - 1.0).abs() < 1e-14);
        assert!((rotated.as_array()[1][1] - 4.0).abs() < 1e-14);
        assert!((rotated.as_array()[2][2] - 9.0).abs() < 1e-14);
    }

    #[test]
    fn symmetric_rotated_by_preserves_symmetry() {
        use qtty::angular::Radians;
        // Rotate a full symmetric matrix by 45° around Z.
        let upper = [[4.0, 1.0, 0.0], [99.0, 9.0, 0.0], [99.0, 99.0, 1.0]];
        let m = SymmetricFrameMatrix3::<F1>::from_upper(upper);
        let r = Rotation3::rz(Radians::new(std::f64::consts::FRAC_PI_4));
        let rotated: SymmetricFrameMatrix3<F2> = m.rotated_by(&r);
        let a = rotated.as_array();
        // Check symmetry.
        for i in 0..3 {
            for j in 0..3 {
                assert!((a[i][j] - a[j][i]).abs() < 1e-13, "a[{i}][{j}] != a[{j}][{i}]");
            }
        }
        // Trace is invariant under rotation similarity.
        let trace_in = 4.0 + 9.0 + 1.0;
        let trace_out = a[0][0] + a[1][1] + a[2][2];
        assert!((trace_out - trace_in).abs() < 1e-12, "trace changed: {trace_out} != {trace_in}");
    }
}
