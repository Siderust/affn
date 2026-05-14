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
use core::ops::Mul;

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
        Self {
            data,
            _frame: PhantomData,
        }
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
        for (i, row) in out.iter_mut().enumerate() {
            for (j, slot) in row.iter_mut().enumerate() {
                *slot = self.data[j][i];
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
        FrameMatrix3 {
            data: self.data,
            _frame: PhantomData,
        }
    }
}

impl<F> FrameMatrix3<F> {
    /// 3×3 identity matrix in frame `F`.
    pub fn identity() -> Self {
        let mut d = [[0.0_f64; 3]; 3];
        for (i, row) in d.iter_mut().enumerate() {
            row[i] = 1.0;
        }
        Self::from_array(d)
    }

    /// Diagonal matrix with the given elements on the diagonal and zeros elsewhere.
    pub fn from_diagonal(diag: [f64; 3]) -> Self {
        let mut d = [[0.0_f64; 3]; 3];
        for i in 0..3 {
            d[i][i] = diag[i];
        }
        Self::from_array(d)
    }

    /// Matrix–matrix product `self · rhs`, frame-tag preserving.
    ///
    /// Both operands must be expressed in the same frame `F`.
    pub fn mat_mul(&self, rhs: &Self) -> Self {
        let a = &self.data;
        let b = &rhs.data;
        let mut out = [[0.0_f64; 3]; 3];
        for (i, out_row) in out.iter_mut().enumerate() {
            for (k, &aik) in a[i].iter().enumerate() {
                if aik == 0.0 {
                    continue;
                }
                for (j, out_elt) in out_row.iter_mut().enumerate() {
                    *out_elt += aik * b[k][j];
                }
            }
        }
        FrameMatrix3::from_array(out)
    }

    /// Add `other` into `self` element-wise, in place.
    pub fn add_in_place(&mut self, other: &FrameMatrix3<F>) {
        for i in 0..3 {
            for j in 0..3 {
                self.data[i][j] += other.data[i][j];
            }
        }
    }

    /// Multiply every element by the scalar `s`, in place.
    pub fn scale_in_place(&mut self, s: f64) {
        for row in &mut self.data {
            for v in row.iter_mut() {
                *v *= s;
            }
        }
    }

    /// Add the outer product `a ⊗ b` (i.e. `aᵢ · bⱼ`) into `self` in place.
    pub fn add_outer_product_in_place(&mut self, a: [f64; 3], b: [f64; 3]) {
        for (i, data_row) in self.data.iter_mut().enumerate() {
            for (j, data_elt) in data_row.iter_mut().enumerate() {
                *data_elt += a[i] * b[j];
            }
        }
    }

    // -------------------------------------------------------------------------
    // Similarity transforms
    // -------------------------------------------------------------------------

    /// General similarity transform `self · m · selfᵀ`, relabelling the result
    /// as frame `G`.
    ///
    /// Treat `self` as a rotation matrix `R : F → G` (rows of `self` are the
    /// basis vectors of `G` expressed in `F`). Given a general matrix `m` in
    /// frame `F`, this computes `R · m · Rᵀ` and tags the result as belonging
    /// to frame `G`.
    ///
    /// For covariance-like inputs that must remain symmetric, use
    /// [`FrameMatrix3::similarity`] instead, which also numerically re-symmetrises
    /// the output.
    pub fn similarity_general<G>(&self, m: &FrameMatrix3<F>) -> FrameMatrix3<G> {
        let r = &self.data;
        let mut tmp = [[0.0_f64; 3]; 3];
        for (i, tmp_row) in tmp.iter_mut().enumerate() {
            for (k, &rik) in r[i].iter().enumerate() {
                if rik == 0.0 {
                    continue;
                }
                for (j, tmp_elt) in tmp_row.iter_mut().enumerate() {
                    *tmp_elt += rik * m.data[k][j];
                }
            }
        }
        // result = tmp · Rᵀ  (Rᵀ[k][j] = R[j][k])
        let mut res = [[0.0_f64; 3]; 3];
        for (i, res_row) in res.iter_mut().enumerate() {
            for (k, &tik) in tmp[i].iter().enumerate() {
                if tik == 0.0 {
                    continue;
                }
                for (j, res_elt) in res_row.iter_mut().enumerate() {
                    *res_elt += tik * r[j][k];
                }
            }
        }
        FrameMatrix3::from_array(res)
    }

    /// Symmetric similarity transform `self · m · selfᵀ`, returning a
    /// [`SymmetricFrameMatrix3<G>`].
    ///
    /// Treat `self` as a rotation matrix `R : F → G`. Given a symmetric matrix
    /// `m` in frame `F`, the result `R · m · Rᵀ` is algebraically symmetric. A
    /// final symmetrisation step averages `(result[i][j] + result[j][i]) / 2`
    /// to prevent floating-point drift.
    ///
    /// For a general (non-symmetric) matrix, use [`FrameMatrix3::similarity_general`].
    pub fn similarity<G>(&self, m: &SymmetricFrameMatrix3<F>) -> SymmetricFrameMatrix3<G> {
        // Compute R · m · Rᵀ via two passes.
        let r = &self.data;
        let mut tmp = [[0.0_f64; 3]; 3];
        for (i, tmp_row) in tmp.iter_mut().enumerate() {
            for (k, &rik) in r[i].iter().enumerate() {
                if rik == 0.0 {
                    continue;
                }
                for (j, tmp_elt) in tmp_row.iter_mut().enumerate() {
                    *tmp_elt += rik * m.data[k][j];
                }
            }
        }
        let mut raw = [[0.0_f64; 3]; 3];
        for (i, raw_row) in raw.iter_mut().enumerate() {
            for (k, &tik) in tmp[i].iter().enumerate() {
                if tik == 0.0 {
                    continue;
                }
                for (j, raw_elt) in raw_row.iter_mut().enumerate() {
                    *raw_elt += tik * r[j][k];
                }
            }
        }
        // Symmetrize to guard against floating-point drift.
        let mut data = [[0.0_f64; 3]; 3];
        for (i, row) in data.iter_mut().enumerate() {
            for (j, slot) in row.iter_mut().enumerate() {
                *slot = 0.5 * (raw[i][j] + raw[j][i]);
            }
        }
        SymmetricFrameMatrix3 {
            data,
            _frame: PhantomData,
        }
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
        for (i, tmp_row) in tmp.iter_mut().enumerate() {
            for (k, &rik) in rm[i].iter().enumerate() {
                if rik == 0.0 {
                    continue;
                }
                for (j, tmp_elt) in tmp_row.iter_mut().enumerate() {
                    *tmp_elt += rik * self.data[k][j];
                }
            }
        }
        // result = tmp · Rᵀ  (Rᵀ[k][j] = R[j][k])
        let mut res = [[0.0_f64; 3]; 3];
        for (i, res_row) in res.iter_mut().enumerate() {
            for (k, &tik) in tmp[i].iter().enumerate() {
                if tik == 0.0 {
                    continue;
                }
                for (j, res_elt) in res_row.iter_mut().enumerate() {
                    *res_elt += tik * rm[j][k];
                }
            }
        }
        FrameMatrix3::from_array(res)
    }
}

// ---------------------------------------------------------------------------
// Operator overloads for FrameMatrix3
// ---------------------------------------------------------------------------

/// Matrix multiplication `A * B → A·B` (frame-tag preserving).
impl<F> Mul<FrameMatrix3<F>> for FrameMatrix3<F> {
    type Output = FrameMatrix3<F>;
    #[inline]
    fn mul(self, rhs: FrameMatrix3<F>) -> FrameMatrix3<F> {
        self.mat_mul(&rhs)
    }
}

/// Matrix multiplication by reference `&A * &B → A·B`.
impl<F> Mul<&FrameMatrix3<F>> for &FrameMatrix3<F> {
    type Output = FrameMatrix3<F>;
    #[inline]
    fn mul(self, rhs: &FrameMatrix3<F>) -> FrameMatrix3<F> {
        self.mat_mul(rhs)
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
        Self {
            data,
            _frame: PhantomData,
        }
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
        Self {
            data: out,
            _frame: PhantomData,
        }
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
        Self {
            data: self.data,
            _frame: PhantomData,
        }
    }

    /// Re-tag the matrix as belonging to frame `G`, without changing data.
    #[inline]
    pub fn relabel<G>(self) -> SymmetricFrameMatrix3<G, T> {
        SymmetricFrameMatrix3 {
            data: self.data,
            _frame: PhantomData,
        }
    }
}

impl<F> SymmetricFrameMatrix3<F> {
    /// 3×3 identity matrix in frame `F`.
    pub fn identity() -> Self {
        Self::from_diagonal([1.0, 1.0, 1.0])
    }

    /// Add `other` into `self` element-wise, in place.
    ///
    /// The caller is responsible for ensuring `other` is symmetric; no
    /// additional symmetrisation is performed.
    pub fn add_in_place(&mut self, other: &SymmetricFrameMatrix3<F>) {
        for i in 0..3 {
            for j in 0..3 {
                self.data[i][j] += other.data[i][j];
            }
        }
    }

    /// Multiply every element by the scalar `s`, in place.
    pub fn scale_in_place(&mut self, s: f64) {
        for row in &mut self.data {
            for v in row.iter_mut() {
                *v *= s;
            }
        }
    }

    /// Add the symmetric outer product `a ⊗ aᵀ` (i.e. `aᵢ · aⱼ`) into `self`
    /// in place.
    ///
    /// Because `a ⊗ aᵀ` is always symmetric, the result remains symmetric.
    pub fn add_outer_product_in_place(&mut self, a: [f64; 3]) {
        for i in 0..3 {
            for j in 0..3 {
                self.data[i][j] += a[i] * a[j];
            }
        }
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
        for (i, tmp_row) in tmp.iter_mut().enumerate() {
            for (k, &rik) in rm[i].iter().enumerate() {
                if rik == 0.0 {
                    continue;
                }
                for (j, tmp_elt) in tmp_row.iter_mut().enumerate() {
                    *tmp_elt += rik * self.data[k][j];
                }
            }
        }
        // raw = tmp · Rᵀ
        let mut raw = [[0.0_f64; 3]; 3];
        for (i, raw_row) in raw.iter_mut().enumerate() {
            for (k, &tik) in tmp[i].iter().enumerate() {
                if tik == 0.0 {
                    continue;
                }
                for (j, raw_elt) in raw_row.iter_mut().enumerate() {
                    *raw_elt += tik * rm[j][k];
                }
            }
        }
        // Symmetrize to guard against floating-point drift.
        let mut data = [[0.0_f64; 3]; 3];
        for (i, row) in data.iter_mut().enumerate() {
            for (j, slot) in row.iter_mut().enumerate() {
                *slot = 0.5 * (raw[i][j] + raw[j][i]);
            }
        }
        SymmetricFrameMatrix3 {
            data,
            _frame: PhantomData,
        }
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
        fn frame_name() -> &'static str {
            "F1"
        }
    }

    #[derive(Debug, Copy, Clone)]
    struct F2;
    impl crate::frames::ReferenceFrame for F2 {
        fn frame_name() -> &'static str {
            "F2"
        }
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
        for (i, row) in m.as_array().iter().enumerate() {
            for (j, value) in row.iter().enumerate() {
                let expected = if i == j { 1.0 } else { 0.0 };
                assert_eq!(*value, expected);
            }
        }
    }

    #[test]
    fn frame_matrix3_transpose() {
        let data = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
        let m = FrameMatrix3::<F1>::from_array(data);
        let t = m.transpose();
        for (i, row) in t.as_array().iter().enumerate() {
            for (j, value) in row.iter().enumerate() {
                assert_eq!(*value, data[j][i]);
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
        for (i, row) in rotated.as_array().iter().enumerate() {
            for (j, value) in row.iter().enumerate() {
                assert!((*value - data[i][j]).abs() < 1e-14);
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
        for (i, row) in m.as_array().iter().enumerate() {
            for (j, value) in row.iter().enumerate() {
                if i != j {
                    assert_eq!(*value, 0.0);
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
        for (i, row) in a.iter().enumerate() {
            for (j, value) in row.iter().enumerate() {
                assert!(
                    (*value - a[j][i]).abs() < 1e-13,
                    "a[{i}][{j}] != a[{j}][{i}]"
                );
            }
        }
        // Trace is invariant under rotation similarity.
        let trace_in = 4.0 + 9.0 + 1.0;
        let trace_out = a[0][0] + a[1][1] + a[2][2];
        assert!(
            (trace_out - trace_in).abs() < 1e-12,
            "trace changed: {trace_out} != {trace_in}"
        );
    }

    // -------------------------------------------------------------------------
    // New algebra: mat_mul, from_diagonal, similarity, in-place ops
    // -------------------------------------------------------------------------

    #[test]
    fn frame_matrix3_from_diagonal() {
        let m = FrameMatrix3::<F1>::from_diagonal([2.0, 3.0, 5.0]);
        let a = m.as_array();
        assert_eq!(a[0][0], 2.0);
        assert_eq!(a[1][1], 3.0);
        assert_eq!(a[2][2], 5.0);
        assert_eq!(a[0][1], 0.0);
        assert_eq!(a[1][2], 0.0);
    }

    #[test]
    fn frame_matrix3_mat_mul_identity() {
        // A * I = A
        let data = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
        let a = FrameMatrix3::<F1>::from_array(data);
        let eye = FrameMatrix3::<F1>::identity();
        let result = a.mat_mul(&eye);
        for (i, row) in result.as_array().iter().enumerate() {
            for (j, v) in row.iter().enumerate() {
                assert!(
                    (*v - data[i][j]).abs() < 1e-14,
                    "A*I mismatch at [{i}][{j}]: {v} != {}",
                    data[i][j]
                );
            }
        }
    }

    #[test]
    fn frame_matrix3_mat_mul_known() {
        // A = [[1,2],[3,4],[0,0]] (3x3 padded), B = [[5,6],[7,8],[0,0]] (padded)
        // A·B[0][0] = 1*5 + 2*7 + 0 = 19; A·B[0][1] = 1*6 + 2*8 = 22
        // A·B[1][0] = 3*5 + 4*7 = 43; A·B[1][1] = 3*6 + 4*8 = 50
        let a = FrameMatrix3::<F1>::from_array([[1.0, 2.0, 0.0], [3.0, 4.0, 0.0], [0.0, 0.0, 1.0]]);
        let b = FrameMatrix3::<F1>::from_array([[5.0, 6.0, 0.0], [7.0, 8.0, 0.0], [0.0, 0.0, 1.0]]);
        let c = a.mat_mul(&b);
        assert!((c.as_array()[0][0] - 19.0).abs() < 1e-14);
        assert!((c.as_array()[0][1] - 22.0).abs() < 1e-14);
        assert!((c.as_array()[1][0] - 43.0).abs() < 1e-14);
        assert!((c.as_array()[1][1] - 50.0).abs() < 1e-14);
        assert!((c.as_array()[2][2] - 1.0).abs() < 1e-14);
    }

    #[test]
    fn frame_matrix3_mul_operator() {
        let eye = FrameMatrix3::<F1>::identity();
        let result = eye * eye;
        assert_eq!(result.as_array(), eye.as_array());
    }

    #[test]
    fn frame_matrix3_similarity_general_identity_rotation() {
        let data = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
        let m = FrameMatrix3::<F1>::from_array(data);
        let eye = FrameMatrix3::<F1>::identity();
        let result: FrameMatrix3<F2> = eye.similarity_general(&m);
        for (i, row) in result.as_array().iter().enumerate() {
            for (j, v) in row.iter().enumerate() {
                assert!(
                    (*v - data[i][j]).abs() < 1e-14,
                    "sim_general identity failed at [{i}][{j}]"
                );
            }
        }
    }

    #[test]
    fn frame_matrix3_similarity_round_trip() {
        use qtty::angular::Radians;
        // rotate diagonal cov by 45° around Z, then back
        let m = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 4.0, 9.0]);
        let r45 = Rotation3::rz(Radians::new(std::f64::consts::FRAC_PI_4));
        let r45_mat = FrameMatrix3::<F1>::from_array(*r45.as_matrix());
        let rotated: SymmetricFrameMatrix3<F2> = r45_mat.similarity(&m);

        let r45_inv = r45.inverse();
        let r45_inv_mat = FrameMatrix3::<F2>::from_array(*r45_inv.as_matrix());
        let back: SymmetricFrameMatrix3<F1> = r45_inv_mat.similarity(&rotated);
        let orig = m.as_array();
        let result = back.as_array();
        for i in 0..3 {
            for j in 0..3 {
                assert!(
                    (result[i][j] - orig[i][j]).abs() < 1e-12,
                    "round-trip similarity failed at [{i}][{j}]: {} != {}",
                    result[i][j],
                    orig[i][j]
                );
            }
        }
    }

    #[test]
    fn frame_matrix3_in_place_ops() {
        let mut m = FrameMatrix3::<F1>::from_diagonal([1.0, 2.0, 3.0]);
        let other = FrameMatrix3::<F1>::from_diagonal([1.0, 1.0, 1.0]);
        m.add_in_place(&other);
        assert_eq!(m.as_array()[0][0], 2.0);
        assert_eq!(m.as_array()[1][1], 3.0);
        assert_eq!(m.as_array()[2][2], 4.0);
        m.scale_in_place(2.0);
        assert_eq!(m.as_array()[0][0], 4.0);
        m.add_outer_product_in_place([1.0, 0.0, 0.0], [0.0, 1.0, 0.0]);
        assert_eq!(m.as_array()[0][1], 1.0);
    }

    #[test]
    fn symmetric_in_place_ops() {
        let mut m = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 2.0, 3.0]);
        let other = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 1.0, 1.0]);
        m.add_in_place(&other);
        assert_eq!(m.diagonal(), [2.0, 3.0, 4.0]);
        m.scale_in_place(0.5);
        assert_eq!(m.diagonal(), [1.0, 1.5, 2.0]);
        m.add_outer_product_in_place([1.0, 0.0, 0.0]);
        assert_eq!(m.as_array()[0][0], 2.0);
        assert_eq!(m.as_array()[0][1], 0.0); // stays symmetric
    }
}
