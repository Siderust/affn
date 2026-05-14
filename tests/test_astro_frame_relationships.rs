//! Tests for the canonical identity relationships among the IAU/IERS markers
//! `ICRS`, `ICRF`, and `GCRS` exposed by `affn::frames::astro`.
//!
//! Frame-bias tests (GCRS ↔ EME2000) live in `siderust::astro::frame_bias`.
//!
//! Conventions checked here:
//!
//! * `ICRS` ↔ `ICRF`: the direction-frame rotation is exactly
//!   `Rotation3::IDENTITY` (bit-equal — no FP tolerance).
//! * `ICRS` ↔ `GCRS`: as a *direction* frame, GCRS is bit-identical to ICRS
//!   (per IAU 2000 Resolution B1.3); the only difference is the spatial
//!   origin, encoded by the center type.

#![cfg(feature = "astro")]

use affn::frames::{GCRS, ICRF, ICRS};
use affn::ops::Rotation3;

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
