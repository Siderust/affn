//! Ellipsoidal coordinate types.
//!
//! - [`Position<C, F, U>`]: an ellipsoidal **position** (longitude, latitude,
//!   height above the reference ellipsoid)
//!
//! This module is the ellipsoidal analogue of [`spherical`](crate::spherical) and
//! [`cartesian`](crate::cartesian).  The reference frame `F` determines _which_
//! ellipsoid is used via the [`HasEllipsoid`](crate::ellipsoid::HasEllipsoid)
//! trait, so conversions to Cartesian are compile-time gated on the frame.
//!
//! # Why a separate coordinate family?
//!
//! An ellipsoidal (geodetic) position cannot be represented as a spherical
//! `Position<C, F, U>` without silently losing meaning:
//!
//! - In a spherical position, `distance` is the **radial distance** from the
//!   origin, *not* the height above an ellipsoid.
//! - Calling `.to_cartesian()` on a spherical position performs a spherical →
//!   Cartesian conversion, which is **geometrically wrong** for geodetic
//!   heights.
//!
//! By using a dedicated `ellipsoidal::Position`, callers must go through an
//! explicit, ellipsoid-aware conversion.

pub mod position;
pub use position::Position;

// =============================================================================
// Shared normalisation helpers
// =============================================================================

/// Normalise geodetic longitude/latitude to their canonical ranges.
///
/// - `lon` → `[-180°, +180°)`
/// - `lat` → `[-90°, +90°]` (pole-crossing reflected into longitude)
pub(crate) fn normalize_lon_lat(lon_deg: f64, lat_deg: f64) -> (f64, f64) {
    let mut lat = (lat_deg + 90.0).rem_euclid(360.0) - 90.0;
    let mut lon = lon_deg;

    if lat > 90.0 {
        lat = 180.0 - lat;
        lon += 180.0;
    }

    lon = (lon + 180.0).rem_euclid(360.0) - 180.0;
    (lon, lat)
}
