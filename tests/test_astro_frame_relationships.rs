//! Tests for the canonical relationships among the four IAU/IERS markers
//! `ICRS`, `ICRF`, `EME2000`, `GCRS` exposed by `affn::frames::astro`.
//!
//! Conventions checked here:
//!
//! * `ICRS` ↔ `ICRF`: the direction-frame rotation is exactly
//!   `Rotation3::IDENTITY` (bit-equal — no FP tolerance).
//! * `ICRS` ↔ `GCRS`: as a *direction* frame, GCRS is bit-identical to ICRS
//!   (per IAU 2000 Resolution B1.3); the only difference is the spatial
//!   origin, encoded by the center type.
//! * `GCRS` ↔ `EME2000`: a constant frame-bias rotation `B` of magnitude
//!   ≈ 23 mas (≈ 1.1 × 10⁻⁷ rad), as documented in IERS Conventions (2010)
//!   §5.4.4 / Table 5.2b.

#![cfg(feature = "astro")]

use affn::frames::{EME2000, GCRS, ICRF, ICRS};
use affn::ops::Rotation3;

/// Convert a `Rotation3` to its rotation angle (radians) via the trace.
fn rotation_angle_rad(r: &Rotation3) -> f64 {
    let m = r.as_matrix();
    let trace = m[0][0] + m[1][1] + m[2][2];
    let cos = ((trace - 1.0) * 0.5).clamp(-1.0, 1.0);
    cos.acos()
}

/// Maximum elementwise absolute difference between two 3×3 rotation matrices,
/// useful as an angular-separation proxy on rotation matrices that are very
/// close to identity (where the trace-based formula loses precision).
fn max_abs_diff(a: &Rotation3, b: &Rotation3) -> f64 {
    let am = a.as_matrix();
    let bm = b.as_matrix();
    let mut max = 0.0_f64;
    for i in 0..3 {
        for j in 0..3 {
            let d = (am[i][j] - bm[i][j]).abs();
            if d > max {
                max = d;
            }
        }
    }
    max
}

// ─────────────────────────────────────────────────────────────────────────────
// ICRS ↔ ICRF
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn icrs_to_icrf_is_bit_exact_identity() {
    // ICRS → ICRF must be the literal identity rotation, not just close.
    let r = ICRS::direction_rotation_to_icrf();
    assert_eq!(r, Rotation3::IDENTITY);
    assert_eq!(r.as_matrix(), Rotation3::IDENTITY.as_matrix());
}

#[test]
fn icrf_to_icrs_is_bit_exact_identity() {
    let r = ICRF::direction_rotation_to_icrs();
    assert_eq!(r, Rotation3::IDENTITY);
    assert_eq!(r.as_matrix(), Rotation3::IDENTITY.as_matrix());
}

// ─────────────────────────────────────────────────────────────────────────────
// ICRS ↔ GCRS  (direction-only)
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn icrs_to_gcrs_direction_is_bit_exact_identity() {
    // Per IAU 2000 Resolution B1.3, GCRS axes are kinematically non-rotating
    // w.r.t. ICRS — the direction-frame rotation is *exactly* the identity.
    let r = ICRS::direction_rotation_to_gcrs();
    assert_eq!(r, Rotation3::IDENTITY);
}

#[test]
fn gcrs_to_icrs_direction_is_bit_exact_identity() {
    let r = GCRS::direction_rotation_to_icrs();
    assert_eq!(r, Rotation3::IDENTITY);
}

// ─────────────────────────────────────────────────────────────────────────────
// GCRS ↔ EME2000  (frame bias B; IERS Conventions 2010 §5.4.4 / Table 5.2b)
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn gcrs_to_eme2000_frame_bias_magnitude_is_about_23_mas() {
    let b = GCRS::frame_bias_to_eme2000();

    // ~23 mas ≈ 1.115e-7 rad. Bound generously (1e-8 .. 5e-7 rad, i.e.
    // ~2 mas .. ~100 mas) to lock down the order of magnitude without
    // pinning it to a specific PFW06/IERS variant down to the last bit.
    let theta = rotation_angle_rad(&b);
    assert!(
        (1.0e-8..5.0e-7).contains(&theta),
        "frame-bias angle {theta:e} rad is outside the documented ≈23 mas range",
    );

    // Tighter sanity: ~23 mas == 23e-3 * pi/648000 rad ≈ 1.115e-7.
    let nominal = 23.0e-3 * std::f64::consts::PI / 648_000.0;
    assert!(
        (theta - nominal).abs() < 0.5 * nominal,
        "frame-bias angle {theta:e} rad differs from the nominal 23 mas \
         ({nominal:e} rad) by more than 50%",
    );
}

#[test]
fn gcrs_to_eme2000_is_not_identity() {
    // Sanity: the bias is *not* zero — that would silently mean we are
    // treating GCRS and EME2000 as the same frame, which is wrong.
    let b = GCRS::frame_bias_to_eme2000();
    assert_ne!(b, Rotation3::IDENTITY);
    assert!(max_abs_diff(&b, &Rotation3::IDENTITY) > 1.0e-9);
}

#[test]
fn gcrs_eme2000_roundtrip_is_identity_to_1e_minus_15() {
    // Round-trip GCRS → EME2000 → GCRS must be the identity to within
    // double-precision noise (well under 1e-15 angular separation).
    let fwd = GCRS::frame_bias_to_eme2000();
    let inv = EME2000::frame_bias_to_gcrs();
    let round = fwd * inv;

    let diff = max_abs_diff(&round, &Rotation3::IDENTITY);
    assert!(
        diff < 1.0e-15,
        "GCRS→EME2000→GCRS deviates from identity by {diff:e} \
         (> 1e-15 angular separation)",
    );

    // And in the other direction.
    let round_other = inv * fwd;
    let diff_other = max_abs_diff(&round_other, &Rotation3::IDENTITY);
    assert!(
        diff_other < 1.0e-15,
        "EME2000→GCRS→EME2000 deviates from identity by {diff_other:e}",
    );
}

#[test]
fn icrs_and_gcrs_share_the_same_frame_bias_to_eme2000() {
    // Because GCRS and ICRS are direction-identical, their frame-bias
    // rotations to EME2000 must be the *same* matrix (bit-equal).
    let from_gcrs = GCRS::frame_bias_to_eme2000();
    let from_icrs = ICRS::frame_bias_to_eme2000();
    assert_eq!(from_gcrs, from_icrs);
}

#[test]
fn frame_bias_off_diagonal_signs_match_iers_convention() {
    // IERS / ERFA convention for the IAU 2006 bias rb at J2000.0:
    //   rb[0][1] < 0, rb[1][0] > 0,
    //   rb[0][2] > 0, rb[2][0] < 0,
    //   rb[1][2] > 0, rb[2][1] < 0.
    // (See `siderust/.../bias.rs::bias_off_diagonal_signs_match_erfa`.)
    let b = GCRS::frame_bias_to_eme2000();
    let m = b.as_matrix();
    assert!(m[0][1] < 0.0, "rb[0][1] should be negative, got {}", m[0][1]);
    assert!(m[1][0] > 0.0, "rb[1][0] should be positive, got {}", m[1][0]);
    assert!(m[0][2] > 0.0, "rb[0][2] should be positive, got {}", m[0][2]);
    assert!(m[2][0] < 0.0, "rb[2][0] should be negative, got {}", m[2][0]);
    assert!(m[1][2] > 0.0, "rb[1][2] should be positive, got {}", m[1][2]);
    assert!(m[2][1] < 0.0, "rb[2][1] should be negative, got {}", m[2][1]);
}
