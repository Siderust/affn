// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Vallés Puig, Ramon

//! # Ellipsoid Module
//!
//! Provides the [`Ellipsoid`] trait for defining geodetic reference ellipsoids,
//! the [`HasEllipsoid`] trait for associating an ellipsoid with a reference frame,
//! and predefined ellipsoid constants ([`Wgs84`], [`Grs80`]).
//!
//! ## Architectural Rationale
//!
//! In geodesy and astrometry:
//!
//! - The **Center** represents the physical origin (e.g., geocenter).
//! - The **Frame** represents the terrestrial reference realization (e.g., ITRF2014).
//! - The **ellipsoid** is tied to the datum / realization of the frame, not
//!   to the physical center.
//!
//! Therefore the ellipsoid is a property of the Frame.  This allows:
//!
//! - Multiple terrestrial realizations with different ellipsoids
//! - Avoiding proliferation of datum-specific centers
//! - Future compatibility with dynamic terrestrial frames (e.g., ITRF20xx)
//!
//! ## Example
//!
//! ```rust,ignore
//! use affn::ellipsoid::{Ellipsoid, HasEllipsoid, Wgs84};
//!
//! // Frames with an ellipsoid attribute get HasEllipsoid for free via derive:
//! //   #[derive(ReferenceFrame)]
//! //   #[frame(ellipsoid = "Wgs84")]
//! //   pub struct ECEF;
//! //
//! // This generates:
//! //   impl HasEllipsoid for ECEF {
//! //       type Ellipsoid = Wgs84;
//! //   }
//! ```

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

// =============================================================================
// Ellipsoid trait
// =============================================================================

/// A geodetic reference ellipsoid defined by its semi-major axis and flattening.
///
/// Implementations are zero-sized marker types carrying the ellipsoid constants
/// as associated `const` items.
///
/// # Parameters
///
/// | Constant | Symbol | Meaning |
/// |----------|--------|---------|
/// | [`A`](Ellipsoid::A) | *a* | Semi-major axis (equatorial radius) in **metres** |
/// | [`F`](Ellipsoid::F) | *f* | Flattening (*f = (a − b) / a*) |
///
/// # Provided Methods
///
/// | Method | Formula | Meaning |
/// |--------|---------|---------|
/// | [`e2`](Ellipsoid::e2) | *2f − f²* | First eccentricity squared |
/// | [`b`](Ellipsoid::b) | *a(1 − f)* | Semi-minor axis (polar radius) in metres |
///
/// # Example
///
/// ```rust
/// use affn::ellipsoid::{Ellipsoid, Wgs84};
///
/// assert!((Wgs84::A - 6_378_137.0).abs() < 1e-6);
/// assert!((Wgs84::e2() - 0.006_694_379_990_14).abs() < 1e-12);
/// ```
pub trait Ellipsoid: Copy + Clone + std::fmt::Debug {
    /// Semi-major axis (equatorial radius) in **metres**.
    const A: f64;

    /// Flattening (*f = (a − b) / a*).
    const F: f64;

    /// First eccentricity squared: *e² = 2f − f²*.
    #[inline]
    fn e2() -> f64 {
        2.0 * Self::F - Self::F * Self::F
    }

    /// Semi-minor axis (polar radius) in metres: *b = a(1 − f)*.
    #[inline]
    fn b() -> f64 {
        Self::A * (1.0 - Self::F)
    }
}

// =============================================================================
// HasEllipsoid trait
// =============================================================================

/// Marker trait associating a [`ReferenceFrame`](crate::frames::ReferenceFrame)
/// with a specific [`Ellipsoid`].
///
/// The `#[derive(ReferenceFrame)]` macro generates this impl automatically
/// when the `ellipsoid` attribute is present:
///
/// ```rust,ignore
/// #[derive(ReferenceFrame)]
/// #[frame(ellipsoid = "Wgs84")]
/// pub struct ECEF;
///
/// // Expands to:
/// // impl HasEllipsoid for ECEF {
/// //     type Ellipsoid = Wgs84;
/// // }
/// ```
///
/// Geodetic conversions are trait-gated on `F: HasEllipsoid`, so they are
/// only available when the frame defines an associated ellipsoid.
pub trait HasEllipsoid {
    /// The reference ellipsoid associated with this frame.
    type Ellipsoid: Ellipsoid;
}

// =============================================================================
// Predefined ellipsoids
// =============================================================================

/// WGS 84 (World Geodetic System 1984) reference ellipsoid.
///
/// The standard ellipsoid used by GPS and most global mapping systems.
///
/// | Parameter | Value |
/// |-----------|-------|
/// | Semi-major axis (*a*) | 6 378 137.0 m |
/// | Flattening (*f*) | 1 / 298.257 223 563 |
/// | First eccentricity² (*e²*) | 0.006 694 379 990 14 |
///
/// # References
///
/// * NIMA TR8350.2, Third Edition (2000)
/// * <https://epsg.org/ellipsoid_7030/WGS-84.html>
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Wgs84;

impl Ellipsoid for Wgs84 {
    const A: f64 = 6_378_137.0;
    const F: f64 = 1.0 / 298.257_223_563;
}

/// GRS 80 (Geodetic Reference System 1980) reference ellipsoid.
///
/// The reference ellipsoid adopted by the IUGG in 1979 and used by ITRF
/// realizations. Numerically almost identical to WGS 84 (they share the
/// same semi-major axis; the flattening differs in the 9th decimal place).
///
/// | Parameter | Value |
/// |-----------|-------|
/// | Semi-major axis (*a*) | 6 378 137.0 m |
/// | Flattening (*f*) | 1 / 298.257 222 101 |
///
/// # References
///
/// * H. Moritz, "Geodetic Reference System 1980", *Bulletin Géodésique* 54 (1980)
/// * <https://epsg.org/ellipsoid_7019/GRS-1980.html>
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Grs80;

impl Ellipsoid for Grs80 {
    const A: f64 = 6_378_137.0;
    const F: f64 = 1.0 / 298.257_222_101;
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wgs84_constants() {
        assert!((Wgs84::A - 6_378_137.0).abs() < 1e-6);
        assert!((Wgs84::F - 1.0 / 298.257_223_563).abs() < 1e-15);
        assert!((Wgs84::e2() - 0.006_694_379_990_14).abs() < 1e-12);
        assert!((Wgs84::b() - 6_356_752.314_245_179).abs() < 1e-3);
    }

    #[test]
    fn grs80_constants() {
        assert!((Grs80::A - 6_378_137.0).abs() < 1e-6);
        assert!((Grs80::F - 1.0 / 298.257_222_101).abs() < 1e-15);
        // GRS80 and WGS84 share the same a, differ slightly in f
        assert!((Grs80::e2() - Wgs84::e2()).abs() < 1e-10);
    }

    #[test]
    fn e2_formula() {
        // e² = 2f - f² for WGS84
        let f = Wgs84::F;
        let expected = 2.0 * f - f * f;
        assert!((Wgs84::e2() - expected).abs() < 1e-15);
    }

    #[test]
    fn semi_minor_axis() {
        // b = a(1 - f)
        let expected = Wgs84::A * (1.0 - Wgs84::F);
        assert!((Wgs84::b() - expected).abs() < 1e-10);
    }
}
