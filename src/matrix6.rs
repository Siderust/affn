// SPDX-License-Identifier: AGPL-3.0-only
// Copyright (C) 2026 Vallés Puig, Ramon

//! Frame-tagged 6×6 matrix and block-diagonal rotation helper.
//!
//! This module provides two types for typed 6-dimensional state-space algebra:
//!
//! - [`FrameMatrix6<F>`] — a general 6×6 matrix stored as a flat `[[f64;6];6]`
//!   array, tagged with the reference frame `F`. Supports constructors, block
//!   accessors, matrix multiplication, transpose, and frame relabelling.
//!
//! - [`BlockDiagRotation6<F>`] — a helper for the block-diagonal rotation
//!   `T = blockdiag(R, R)` that arises when rotating a 6-dimensional Cartesian
//!   state-space covariance or state-transition matrix between frames. All
//!   block operations are performed as independent 3×3 similarity transforms,
//!   avoiding the explicit 6×6 assembly.
//!
//! ## Convention: instantaneous rotation
//!
//! Both types implement the **instantaneous** convention: the rotation basis
//! is treated as constant at the moment of evaluation. The time-derivative
//! `Ṙ` of the rotation (which would introduce Coriolis-like off-diagonal
//! blocks) is *ignored*. This is correct for covariance transport and for
//! STM frame changes when the rotation is evaluated at a fixed epoch.
//!
//! ## Block layout
//!
//! All 6×6 types use `[r, v]` ordering:
//!
//! ```text
//! M = [ top_left   top_right  ]   rows/cols 0..2 = position
//!     [ bot_left   bot_right  ]   rows/cols 3..5 = velocity
//! ```
//!
//! ## Example
//!
//! ```rust
//! use affn::matrix6::{FrameMatrix6, BlockDiagRotation6};
//! use affn::matrix3::{FrameMatrix3, SymmetricFrameMatrix3};
//! use affn::ops::Rotation3;
//! use qtty::angular::Radians;
//!
//! #[derive(Debug, Copy, Clone)]
//! struct F;
//! impl affn::frames::ReferenceFrame for F {
//!     fn frame_name() -> &'static str { "F" }
//! }
//!
//! #[derive(Debug, Copy, Clone)]
//! struct G;
//! impl affn::frames::ReferenceFrame for G {
//!     fn frame_name() -> &'static str { "G" }
//! }
//!
//! // Build a 6×6 identity and verify block round-trip.
//! let eye6 = FrameMatrix6::<F>::identity();
//! let tl = eye6.top_left();
//! assert!((tl.as_array()[0][0] - 1.0).abs() < 1e-15);
//!
//! // Block-diagonal rotation with identity → should be a no-op.
//! let r = Rotation3::IDENTITY;
//! let rot6 = BlockDiagRotation6::<F>::from_rotation(r);
//! let cov = SymmetricFrameMatrix3::<F>::from_diagonal([1.0, 4.0, 9.0]);
//! let zero_rv = FrameMatrix3::<F>::zero();
//! let (rr, rv, vv) = rot6.apply_to_symmetric_blocks::<G>(&cov, &zero_rv, &cov);
//! assert!((rr.as_array()[0][0] - 1.0).abs() < 1e-15);
//! assert!((vv.as_array()[1][1] - 4.0).abs() < 1e-15);
//! let _ = rv; // cross-block is all zeros
//! ```

use core::marker::PhantomData;
use core::ops::Mul;

use crate::matrix3::{FrameMatrix3, SymmetricFrameMatrix3};
use crate::ops::Rotation3;

// =============================================================================
// FrameMatrix6
// =============================================================================

/// Frame-tagged 6×6 matrix stored as a row-major `[[f64; 6]; 6]` array.
///
/// The phantom parameter `F` is the reference frame the matrix is expressed
/// in. The block layout is `[r, v]` ordered: rows/columns 0–2 are the
/// position subspace, rows/columns 3–5 are the velocity subspace.
///
/// Use [`FrameMatrix6::from_blocks`] to construct from four 3×3 blocks, and
/// the `top_left()` / `top_right()` / `bottom_left()` / `bottom_right()`
/// accessors to recover them.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FrameMatrix6<F> {
    data: [[f64; 6]; 6],
    _frame: PhantomData<F>,
}

impl<F> FrameMatrix6<F> {
    // -------------------------------------------------------------------------
    // Constructors
    // -------------------------------------------------------------------------

    /// Wrap a raw row-major 6×6 array as a matrix in frame `F`.
    #[inline]
    pub fn from_array(data: [[f64; 6]; 6]) -> Self {
        Self {
            data,
            _frame: PhantomData,
        }
    }

    /// Zero 6×6 matrix in frame `F`.
    #[inline]
    pub fn zero() -> Self {
        Self::from_array([[0.0; 6]; 6])
    }

    /// 6×6 identity matrix in frame `F`.
    pub fn identity() -> Self {
        let mut d = [[0.0_f64; 6]; 6];
        for (i, row) in d.iter_mut().enumerate() {
            row[i] = 1.0;
        }
        Self::from_array(d)
    }

    /// Construct from four 3×3 blocks in `[r, v]` order:
    ///
    /// ```text
    /// M = [ top_left   top_right  ]
    ///     [ bot_left   bot_right  ]
    /// ```
    pub fn from_blocks(
        top_left: FrameMatrix3<F>,
        top_right: FrameMatrix3<F>,
        bottom_left: FrameMatrix3<F>,
        bottom_right: FrameMatrix3<F>,
    ) -> Self {
        let tl = top_left.as_array();
        let tr = top_right.as_array();
        let bl = bottom_left.as_array();
        let br = bottom_right.as_array();
        let mut d = [[0.0_f64; 6]; 6];
        for (i, d_row) in d.iter_mut().enumerate().take(3) {
            for (j, d_elt) in d_row.iter_mut().enumerate().take(3) {
                *d_elt = tl[i][j];
            }
            for (j, d_elt) in d_row[3..].iter_mut().enumerate() {
                *d_elt = tr[i][j];
            }
        }
        for (i, d_row) in d[3..].iter_mut().enumerate() {
            for (j, d_elt) in d_row.iter_mut().enumerate().take(3) {
                *d_elt = bl[i][j];
            }
            for (j, d_elt) in d_row[3..].iter_mut().enumerate() {
                *d_elt = br[i][j];
            }
        }
        Self::from_array(d)
    }

    // -------------------------------------------------------------------------
    // Accessors
    // -------------------------------------------------------------------------

    /// Borrow the underlying row-major 6×6 array.
    #[inline]
    pub fn as_array(&self) -> &[[f64; 6]; 6] {
        &self.data
    }

    /// Copy the top-left 3×3 block (rows 0–2, cols 0–2) as a [`FrameMatrix3<F>`].
    pub fn top_left(&self) -> FrameMatrix3<F> {
        self.extract_block(0, 0)
    }

    /// Copy the top-right 3×3 block (rows 0–2, cols 3–5) as a [`FrameMatrix3<F>`].
    pub fn top_right(&self) -> FrameMatrix3<F> {
        self.extract_block(0, 3)
    }

    /// Copy the bottom-left 3×3 block (rows 3–5, cols 0–2) as a [`FrameMatrix3<F>`].
    pub fn bottom_left(&self) -> FrameMatrix3<F> {
        self.extract_block(3, 0)
    }

    /// Copy the bottom-right 3×3 block (rows 3–5, cols 3–5) as a [`FrameMatrix3<F>`].
    pub fn bottom_right(&self) -> FrameMatrix3<F> {
        self.extract_block(3, 3)
    }

    fn extract_block(&self, row_off: usize, col_off: usize) -> FrameMatrix3<F> {
        let mut out = [[0.0_f64; 3]; 3];
        for (i, out_row) in out.iter_mut().enumerate() {
            for (j, out_elt) in out_row.iter_mut().enumerate() {
                *out_elt = self.data[row_off + i][col_off + j];
            }
        }
        FrameMatrix3::from_array(out)
    }

    // -------------------------------------------------------------------------
    // Operations
    // -------------------------------------------------------------------------

    /// Transpose of this matrix.
    pub fn transpose(&self) -> Self {
        let mut out = [[0.0_f64; 6]; 6];
        for (i, out_row) in out.iter_mut().enumerate() {
            for (j, out_elt) in out_row.iter_mut().enumerate() {
                *out_elt = self.data[j][i];
            }
        }
        Self::from_array(out)
    }

    /// Matrix–matrix product `self · rhs`, frame-tag preserving.
    pub fn mat_mul(&self, rhs: &Self) -> Self {
        let a = &self.data;
        let b = &rhs.data;
        let mut out = [[0.0_f64; 6]; 6];
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
        Self::from_array(out)
    }

    /// Re-tag the matrix as belonging to frame `G`, without changing data.
    ///
    /// Use only when the data is already expressed in `G` by some other means;
    /// the type system cannot verify this.
    #[inline]
    pub fn relabel<G>(self) -> FrameMatrix6<G> {
        FrameMatrix6 {
            data: self.data,
            _frame: PhantomData,
        }
    }
}

/// Matrix multiplication `A * B → A·B` (frame-tag preserving).
impl<F> Mul<FrameMatrix6<F>> for FrameMatrix6<F> {
    type Output = FrameMatrix6<F>;
    #[inline]
    fn mul(self, rhs: FrameMatrix6<F>) -> FrameMatrix6<F> {
        self.mat_mul(&rhs)
    }
}

/// Matrix multiplication by reference `&A * &B → A·B`.
impl<F> Mul<&FrameMatrix6<F>> for &FrameMatrix6<F> {
    type Output = FrameMatrix6<F>;
    #[inline]
    fn mul(self, rhs: &FrameMatrix6<F>) -> FrameMatrix6<F> {
        self.mat_mul(rhs)
    }
}

// =============================================================================
// BlockDiagRotation6
// =============================================================================

/// Block-diagonal rotation `T = blockdiag(R, R)` for 6-dimensional state-space
/// transforms.
///
/// Given a 3×3 rotation `R`, this type represents the 6×6 operator
///
/// ```text
/// T = [ R  0 ]
///     [ 0  R ]
/// ```
///
/// which simultaneously rotates the position and velocity sub-blocks by the
/// same rotation `R`.
///
/// ## Instantaneous convention
///
/// The time-derivative `Ṙ` of the rotation is **ignored**. This is the
/// correct choice for instantaneous covariance and STM frame changes at a
/// fixed epoch. If Coriolis corrections are required (e.g., for a rotating
/// atmosphere drag model), apply them separately.
///
/// ## Efficient block-wise computation
///
/// Instead of assembling and multiplying the full 6×6 matrix, all transforms
/// are performed as three independent 3×3 similarity operations:
///
/// ```text
/// T · M · Tᵀ = [ R·Mrr·Rᵀ   R·Mrv·Rᵀ ]
///               [ R·Mvr·Rᵀ   R·Mvv·Rᵀ ]
/// ```
///
/// For symmetric `M` (covariance) `Mvr = Mrvᵀ` and the result is again
/// symmetric, which is exploited in [`BlockDiagRotation6::apply_to_symmetric_blocks`].
#[derive(Debug, Clone, Copy)]
pub struct BlockDiagRotation6<F> {
    /// The 3×3 rotation matrix R stored as a [`FrameMatrix3<F>`].
    ///
    /// Semantically, rows of `r` are the basis vectors of the *target* frame
    /// expressed in frame `F`, i.e. `R` transforms vectors from `F` to the
    /// target frame `G`.
    r: FrameMatrix3<F>,
}

impl<F> BlockDiagRotation6<F> {
    /// Construct from a [`Rotation3`].
    ///
    /// The rotation `r` should encode the transform `R : F → G` for whatever
    /// target frame `G` the methods are called with.
    #[inline]
    pub fn from_rotation(r: Rotation3) -> Self {
        Self {
            r: FrameMatrix3::from_array(*r.as_matrix()),
        }
    }

    /// Construct from a [`FrameMatrix3<F>`] (e.g., a precomputed rotation
    /// matrix from the local-orbital-frame construction).
    #[inline]
    pub fn from_matrix(r: FrameMatrix3<F>) -> Self {
        Self { r }
    }

    /// Apply `T · M · Tᵀ` (with `T = blockdiag(R, R)`) to a general 6×6
    /// matrix `m6`, returning the result tagged as frame `G`.
    ///
    /// The computation is performed block-wise:
    ///
    /// ```text
    /// T · M · Tᵀ = [ R · Mrr · Rᵀ   R · Mrv · Rᵀ ]
    ///               [ R · Mvr · Rᵀ   R · Mvv · Rᵀ ]
    /// ```
    ///
    /// No assumption is made about the symmetry of `m6`.
    pub fn apply_to_state_matrix<G>(&self, m6: &FrameMatrix6<F>) -> FrameMatrix6<G> {
        let tl: FrameMatrix3<G> = self.r.similarity_general(&m6.top_left());
        let tr: FrameMatrix3<G> = self.r.similarity_general(&m6.top_right());
        let bl: FrameMatrix3<G> = self.r.similarity_general(&m6.bottom_left());
        let br: FrameMatrix3<G> = self.r.similarity_general(&m6.bottom_right());
        FrameMatrix6::from_blocks(tl, tr, bl, br)
    }

    /// Apply `T · P · Tᵀ` (with `T = blockdiag(R, R)`) to a symmetric
    /// covariance stored as three 3×3 blocks `(Prr, Prv, Pvv)`.
    ///
    /// The computation is performed block-wise:
    ///
    /// ```text
    /// Prr' = R · Prr · Rᵀ   (symmetric)
    /// Prv' = R · Prv · Rᵀ   (general)
    /// Pvv' = R · Pvv · Rᵀ   (symmetric)
    /// ```
    ///
    /// `Pvr = Prvᵀ` is derived on demand and never stored.
    ///
    /// # Arguments
    ///
    /// * `rr` — position–position covariance block (symmetric).
    /// * `rv` — position–velocity cross-covariance block (general).
    /// * `vv` — velocity–velocity covariance block (symmetric).
    ///
    /// # Returns
    ///
    /// `(rr', rv', vv')` in frame `G`.
    pub fn apply_to_symmetric_blocks<G>(
        &self,
        rr: &SymmetricFrameMatrix3<F>,
        rv: &FrameMatrix3<F>,
        vv: &SymmetricFrameMatrix3<F>,
    ) -> (
        SymmetricFrameMatrix3<G>,
        FrameMatrix3<G>,
        SymmetricFrameMatrix3<G>,
    ) {
        let rr_out: SymmetricFrameMatrix3<G> = self.r.similarity(rr);
        let rv_out: FrameMatrix3<G> = self.r.similarity_general(rv);
        let vv_out: SymmetricFrameMatrix3<G> = self.r.similarity(vv);
        (rr_out, rv_out, vv_out)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::angular::Radians;

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
    // FrameMatrix6
    // -------------------------------------------------------------------------

    #[test]
    fn frame_matrix6_from_to_array_round_trip() {
        let mut data = [[0.0_f64; 6]; 6];
        for (i, row) in data.iter_mut().enumerate() {
            for (j, elt) in row.iter_mut().enumerate() {
                *elt = (i * 6 + j) as f64;
            }
        }
        let m = FrameMatrix6::<F1>::from_array(data);
        assert_eq!(m.as_array(), &data);
    }

    #[test]
    fn frame_matrix6_identity() {
        let eye = FrameMatrix6::<F1>::identity();
        for (i, row) in eye.as_array().iter().enumerate() {
            for (j, &val) in row.iter().enumerate() {
                let expected = if i == j { 1.0 } else { 0.0 };
                assert_eq!(val, expected);
            }
        }
    }

    #[test]
    fn frame_matrix6_from_blocks_round_trip() {
        let tl = FrameMatrix3::<F1>::from_diagonal([1.0, 2.0, 3.0]);
        let tr = FrameMatrix3::<F1>::from_diagonal([4.0, 5.0, 6.0]);
        let bl = FrameMatrix3::<F1>::from_diagonal([7.0, 8.0, 9.0]);
        let br = FrameMatrix3::<F1>::from_diagonal([10.0, 11.0, 12.0]);
        let m6 = FrameMatrix6::from_blocks(tl, tr, bl, br);

        let tl2 = m6.top_left();
        let tr2 = m6.top_right();
        let bl2 = m6.bottom_left();
        let br2 = m6.bottom_right();

        assert_eq!(tl2.as_array(), tl.as_array());
        assert_eq!(tr2.as_array(), tr.as_array());
        assert_eq!(bl2.as_array(), bl.as_array());
        assert_eq!(br2.as_array(), br.as_array());
    }

    #[test]
    fn frame_matrix6_mul_identity() {
        let eye = FrameMatrix6::<F1>::identity();
        let result = eye * eye;
        for (i, row) in result.as_array().iter().enumerate() {
            for (j, &val) in row.iter().enumerate() {
                let expected = if i == j { 1.0 } else { 0.0 };
                assert!((val - expected).abs() < 1e-14);
            }
        }
    }

    #[test]
    fn frame_matrix6_mul_block() {
        // Construct M6 from block-diagonal (2, 3, 5 on tl and br), multiply by itself.
        let tl = FrameMatrix3::<F1>::from_diagonal([2.0, 3.0, 5.0]);
        let zero = FrameMatrix3::<F1>::zero();
        let br = FrameMatrix3::<F1>::from_diagonal([7.0, 11.0, 13.0]);
        let m6 = FrameMatrix6::from_blocks(tl, zero, zero, br);
        let m6sq = m6.mat_mul(&m6);
        // (2²=4, 3²=9, 5²=25) in top-left; (7²=49, 11²=121, 13²=169) in bottom-right
        let tl2 = m6sq.top_left();
        let br2 = m6sq.bottom_right();
        assert!((tl2.as_array()[0][0] - 4.0).abs() < 1e-14);
        assert!((tl2.as_array()[1][1] - 9.0).abs() < 1e-14);
        assert!((tl2.as_array()[2][2] - 25.0).abs() < 1e-14);
        assert!((br2.as_array()[0][0] - 49.0).abs() < 1e-14);
        assert!((br2.as_array()[1][1] - 121.0).abs() < 1e-14);
        assert!((br2.as_array()[2][2] - 169.0).abs() < 1e-14);
    }

    #[test]
    fn frame_matrix6_transpose() {
        let tl =
            FrameMatrix3::<F1>::from_array([[1.0, 2.0, 3.0], [0.0, 4.0, 5.0], [0.0, 0.0, 6.0]]);
        let tr = FrameMatrix3::<F1>::from_diagonal([7.0, 8.0, 9.0]);
        let bl = FrameMatrix3::<F1>::zero();
        let br = FrameMatrix3::<F1>::identity();
        let m6 = FrameMatrix6::from_blocks(tl, tr, bl, br);
        let m6t = m6.transpose();
        for (i, row_t) in m6t.as_array().iter().enumerate() {
            for (j, &v) in row_t.iter().enumerate() {
                assert!((v - m6.as_array()[j][i]).abs() < 1e-15);
            }
        }
    }

    #[test]
    fn frame_matrix6_relabel() {
        let eye: FrameMatrix6<F1> = FrameMatrix6::identity();
        let eye2: FrameMatrix6<F2> = eye.relabel();
        assert_eq!(eye2.as_array(), eye.as_array());
    }

    // -------------------------------------------------------------------------
    // BlockDiagRotation6
    // -------------------------------------------------------------------------

    #[test]
    fn block_diag_rotation6_identity_is_noop() {
        let rot6 = BlockDiagRotation6::<F1>::from_rotation(Rotation3::IDENTITY);
        let rr = SymmetricFrameMatrix3::<F1>::from_diagonal([1.0, 4.0, 9.0]);
        let rv = FrameMatrix3::<F1>::zero();
        let vv = SymmetricFrameMatrix3::<F1>::from_diagonal([0.01, 0.04, 0.09]);
        let (rr2, rv2, vv2) = rot6.apply_to_symmetric_blocks::<F2>(&rr, &rv, &vv);
        for (i, rr2_row) in rr2.as_array().iter().enumerate() {
            assert!((rr2_row[i] - rr.as_array()[i][i]).abs() < 1e-15);
            assert!((vv2.as_array()[i][i] - vv.as_array()[i][i]).abs() < 1e-15);
            for (j, &val) in rv2.as_array()[i].iter().enumerate() {
                let _ = j; // preserve index binding for clarity
                assert!(val.abs() < 1e-15);
            }
        }
    }

    #[test]
    fn block_diag_rotation6_round_trip() {
        // Rotate by 45° around Z, then rotate back; should recover the original.
        let r_fwd = Rotation3::rz(Radians::new(std::f64::consts::FRAC_PI_4));
        let r_bwd = r_fwd.inverse();

        let rr = SymmetricFrameMatrix3::<F1>::from_upper([
            [4.0, 1.2, 0.5],
            [0.0, 9.0, 0.3],
            [0.0, 0.0, 2.0],
        ]);
        let rv =
            FrameMatrix3::<F1>::from_array([[0.1, 0.02, 0.0], [0.03, 0.2, 0.01], [0.0, 0.0, 0.1]]);
        let vv = SymmetricFrameMatrix3::<F1>::from_upper([
            [0.01, 0.001, 0.0],
            [0.0, 0.02, 0.0],
            [0.0, 0.0, 0.015],
        ]);

        let rot_fwd = BlockDiagRotation6::<F1>::from_rotation(r_fwd);
        let rot_bwd = BlockDiagRotation6::<F2>::from_rotation(r_bwd);

        let (rr2, rv2, vv2) = rot_fwd.apply_to_symmetric_blocks::<F2>(&rr, &rv, &vv);
        let (rr3, rv3, vv3) = rot_bwd.apply_to_symmetric_blocks::<F1>(&rr2, &rv2, &vv2);

        for (i, rr_row) in rr3.as_array().iter().enumerate() {
            for (j, &rr_val) in rr_row.iter().enumerate() {
                let expected_rr = rr.as_array()[i][j];
                assert!(
                    (rr_val - expected_rr).abs() < 1e-12,
                    "rr round-trip failed at [{i}][{j}]: {} != {}",
                    rr_val,
                    expected_rr
                );
            }
            for (j, &rv_val) in rv3.as_array()[i].iter().enumerate() {
                let expected_rv = rv.as_array()[i][j];
                assert!(
                    (rv_val - expected_rv).abs() < 1e-12,
                    "rv round-trip failed at [{i}][{j}]: {} != {}",
                    rv_val,
                    expected_rv
                );
            }
            for (j, &vv_val) in vv3.as_array()[i].iter().enumerate() {
                let expected_vv = vv.as_array()[i][j];
                assert!(
                    (vv_val - expected_vv).abs() < 1e-12,
                    "vv round-trip failed at [{i}][{j}]: {} != {}",
                    vv_val,
                    expected_vv
                );
            }
        }
    }

    #[test]
    fn block_diag_rotation6_apply_to_state_matrix_identity() {
        // T * I6 * T^T = I6 for any rotation T.
        let r = Rotation3::rz(Radians::new(1.23));
        let rot6 = BlockDiagRotation6::<F1>::from_rotation(r);
        let eye6 = FrameMatrix6::<F1>::identity();
        let result: FrameMatrix6<F2> = rot6.apply_to_state_matrix(&eye6);
        // The similarity of the identity block is still the identity block
        for (i, row) in result.as_array().iter().enumerate() {
            for (j, &val) in row.iter().enumerate() {
                let expected = if i == j { 1.0 } else { 0.0 };
                assert!(
                    (val - expected).abs() < 1e-13,
                    "T*I6*T^T mismatch at [{i}][{j}]: {} != {expected}",
                    val
                );
            }
        }
    }
}
