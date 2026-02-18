// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (C) 2026 Vallés Puig, Ramon

//! # Geodesy Module
//!
//! Provides [`GeodeticCoord`], a strongly-typed container for geodetic
//! coordinates (longitude, latitude, ellipsoidal height).
//!
//! ## Why not a spherical `Position`?
//!
//! A geodetic position cannot be represented as a spherical
//! `Position<C, F, U>` without silently losing meaning:
//!
//! - In a spherical position, `distance` is the **radial distance** from
//!   the origin, *not* the height above an ellipsoid.
//! - Calling `.to_cartesian()` on a spherical position performs a
//!   spherical → Cartesian conversion, which is **geometrically wrong** for
//!   geodetic heights. The correct conversion requires the Bowring/Vermeille
//!   formula against a specific ellipsoid (e.g., WGS84).
//!
//! By using a dedicated `GeodeticCoord`, callers must go through an explicit,
//! ellipsoid-aware conversion rather than accidentally calling `.to_cartesian()`.
//!
//! ## Datum
//!
//! `GeodeticCoord` is intentionally **datum-agnostic**: it stores the numbers,
//! but does not embed WGS84 or any other ellipsoid. Datum-specific conversions
//! (geodetic → ECEF) belong to the domain crate (e.g., `siderust`).

use qtty::{Degrees, Meter, Quantity};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A geodetic coordinate triple (longitude, latitude, ellipsoidal height).
///
/// This is a plain, datum-agnostic data container.  Use it to store and
/// pass geodetic positions across API boundaries.
///
/// # Field conventions
///
/// | Field    | Meaning                                    |
/// |----------|--------------------------------------------|
/// | `lon`    | Geodetic longitude, positive **eastward**  |
/// | `lat`    | Geodetic latitude, positive **northward**  |
/// | `height` | Height above the reference ellipsoid (m)   |
///
/// # Correctness note
///
/// Do **not** convert this value using spherical-to-Cartesian formulas.
/// Always use an ellipsoid-aware converter such as
/// `ObserverSite::geocentric_itrf()` (in `siderust`).
///
/// # Example
///
/// ```rust
/// use affn::geodesy::GeodeticCoord;
/// use qtty::*;
///
/// let greenwich = GeodeticCoord {
///     lon: Degrees::new(0.0),
///     lat: Degrees::new(51.4769),
///     height: Meters::new(0.0),
/// };
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct GeodeticCoord {
    /// Geodetic longitude (positive eastward), in degrees.
    pub lon: Degrees,
    /// Geodetic latitude (positive northward), in degrees.
    pub lat: Degrees,
    /// Height above the reference ellipsoid, in meters.
    pub height: Quantity<Meter>,
}

impl GeodeticCoord {
    /// Creates a new geodetic coordinate from longitude, latitude, and height.
    ///
    /// # Arguments
    ///
    /// - `lon`: Geodetic longitude (positive eastward), in degrees.
    /// - `lat`: Geodetic latitude (positive northward), in degrees.
    /// - `height`: Height above the reference ellipsoid, in meters.
    ///
    /// # Note
    ///
    /// This constructor does **not** validate input ranges. For WGS84-validated
    /// construction, use `ObserverSite::try_new` in `siderust`.
    pub fn new(lon: Degrees, lat: Degrees, height: Quantity<Meter>) -> Self {
        Self { lon, lat, height }
    }
}

impl Default for GeodeticCoord {
    /// Returns the geodetic origin: (0°E, 0°N, 0 m).
    fn default() -> Self {
        Self {
            lon: Degrees::new(0.0),
            lat: Degrees::new(0.0),
            height: Quantity::<Meter>::new(0.0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::*;

    #[test]
    fn geodetic_coord_new() {
        let g = GeodeticCoord::new(10.0 * DEG, 20.0 * DEG, 100.0 * M);
        assert_eq!(g.lon, 10.0 * DEG);
        assert_eq!(g.lat, 20.0 * DEG);
        assert_eq!(g.height, 100.0 * M);
    }

    #[test]
    fn geodetic_coord_default() {
        let g = GeodeticCoord::default();
        assert_eq!(g.lon, 0.0 * DEG);
        assert_eq!(g.lat, 0.0 * DEG);
        assert_eq!(g.height, 0.0 * M);
    }

    #[test]
    fn geodetic_coord_equality() {
        let a = GeodeticCoord::new(1.0 * DEG, 2.0 * DEG, 3.0 * M);
        let b = GeodeticCoord::new(1.0 * DEG, 2.0 * DEG, 3.0 * M);
        let c = GeodeticCoord::new(1.0 * DEG, 2.0 * DEG, 4.0 * M);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
}
