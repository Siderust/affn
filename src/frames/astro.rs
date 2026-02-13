// Astronomical reference frames for spherical coordinate systems.
//
// These are feature-gated behind `#[cfg(feature = "astro")]` to keep the
// core `affn` crate domain-agnostic. Enable the `astro` feature to use them.
//
// Because these types are defined in the same crate as `Direction`/`Position`,
// the derive macro can generate inherent named constructors and getters
// (e.g., `.ra()`, `.dec()`, `Direction::<ICRS>::new(ra, dec)`) without
// violating Rust's orphan rules for inherent impls.

use crate::DeriveReferenceFrame;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

// =============================================================================
// Equatorial frames (ra/dec)
// =============================================================================

/// International Celestial Reference System.
///
/// The fundamental celestial reference frame used in modern astronomy.
/// It is quasi-inertial and centered at the solar system barycenter.
/// The axes are defined by the positions of distant quasars.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ICRS;

/// International Celestial Reference Frame (ICRF).
///
/// The physical realisation of the ICRS via VLBI observations of extragalactic
/// sources. DE440 ephemeris data is natively expressed in ICRF.
///
/// Practically coincident with [`ICRS`] to sub-milliarcsecond accuracy, but
/// kept as a distinct type so that DE440 internal vectors carry the correct
/// frame provenance and cannot be accidentally mixed with other equatorial
/// frames without an explicit conversion step.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra")]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ICRF;

/// Mean equator and equinox of J2000.0 (FK5/J2000 mean).
///
/// Earth-based mean equator/equinox at epoch J2000.0, with nutation removed.
/// This is the classic "J2000 equatorial" frame used by many catalogs.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EquatorialMeanJ2000;

/// Mean equator and equinox of date.
///
/// Earth-based mean equator/equinox at a given epoch (precession applied,
/// nutation removed). Requires a TT epoch for transformations.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EquatorialMeanOfDate;

/// True equator and equinox of date.
///
/// Earth-based true equator/equinox at a given epoch (precession + nutation).
/// Requires a TT epoch for transformations.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EquatorialTrueOfDate;

/// Geocentric Celestial Reference System (GCRS).
///
/// The geocentric counterpart of the BCRS (barycentric CRS). Its axes are
/// kinematically non-rotating with respect to the ICRS, but the origin is
/// at the Earth's center of mass. In the IAU 2000/2006 framework, directions
/// expressed in the GCRS are transformed to the terrestrial frame via the
/// CIO-based procedure: GCRS → (CIP X,Y + CIO s) → CIRS → (ERA) → TIRS →
/// (polar motion W) → ITRS.
///
/// For most astronomical purposes (< 1 mas), GCRS ≈ ICRS for directions.
///
/// ## References
/// * IAU 2000 Resolution B1.3
/// * IERS Conventions (2010), §5.1
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct GCRS;

/// Celestial Intermediate Reference System (CIRS).
///
/// An intermediate geocentric equatorial frame whose pole is the **Celestial
/// Intermediate Pole** (CIP) and whose origin on the CIP equator is the
/// **Celestial Intermediate Origin** (CIO). CIRS is obtained from GCRS by
/// applying the CIP (X, Y) coordinates and the CIO locator *s*.
///
/// The CIRS is the "bridge" between the celestial (GCRS) and terrestrial
/// (TIRS) frames in the CIO-based procedure.
///
/// ## References
/// * IAU 2000 Resolution B1.8
/// * IERS Conventions (2010), §5.4.4
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct CIRS;

/// Terrestrial Intermediate Reference System (TIRS).
///
/// An intermediate geocentric frame obtained from CIRS by applying the
/// **Earth Rotation Angle** (ERA). Its pole is the CIP (same as CIRS),
/// but the prime direction on the CIP equator is the **Terrestrial
/// Intermediate Origin** (TIO), which tracks the Earth's rotation.
///
/// The TIRS is connected to the ITRS by the polar motion matrix **W**.
///
/// ## References
/// * IAU 2000 Resolution B1.8
/// * IERS Conventions (2010), §5.4.4
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TIRS;

// =============================================================================
// Horizontal frame (alt/az)
// =============================================================================

/// Local horizon coordinate system.
///
/// A topocentric frame based on the observer's local horizon.
/// Uses altitude (elevation above horizon) and azimuth (bearing from north).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "alt", azimuth = "az", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Horizontal;

// =============================================================================
// Longitude/latitude frames
// =============================================================================

/// Ecliptic coordinate system.
///
/// Based on the plane of Earth's orbit around the Sun.
/// Uses ecliptic longitude and latitude.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Ecliptic;

/// International Terrestrial Reference Frame.
///
/// A geocentric Earth-fixed frame that co-rotates with the Earth.
/// Used for geodetic and geophysical applications.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "altitude", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ITRF;

/// Earth-Centered, Earth-Fixed coordinate system.
///
/// A geocentric Cartesian coordinate system that rotates with the Earth.
/// The X-axis points to the intersection of the prime meridian and equator.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "altitude", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ECEF;

// =============================================================================
// Galactic frame
// =============================================================================

/// Galactic coordinate system.
///
/// Based on the plane of the Milky Way galaxy.
/// Uses galactic longitude and latitude, with the center
/// of the galaxy defining the origin of galactic longitude.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "b", azimuth = "l", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Galactic;

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::centers::{AffineCenter, ReferenceCenter};
    use crate::frames::{ReferenceFrame, SphericalNaming};
    use crate::spherical::{Direction, Position};
    use qtty::*;

    #[test]
    fn test_frame_names() {
        assert_eq!(ICRS::frame_name(), "ICRS");
        assert_eq!(ICRF::frame_name(), "ICRF");
        assert_eq!(Horizontal::frame_name(), "Horizontal");
        assert_eq!(Ecliptic::frame_name(), "Ecliptic");
        assert_eq!(Galactic::frame_name(), "Galactic");
        assert_eq!(ITRF::frame_name(), "ITRF");
        assert_eq!(ECEF::frame_name(), "ECEF");
    }

    #[test]
    fn test_spherical_naming() {
        assert_eq!(ICRS::polar_name(), "dec");
        assert_eq!(ICRS::azimuth_name(), "ra");

        assert_eq!(Horizontal::polar_name(), "alt");
        assert_eq!(Horizontal::azimuth_name(), "az");

        assert_eq!(Ecliptic::polar_name(), "lat");
        assert_eq!(Ecliptic::azimuth_name(), "lon");

        assert_eq!(Galactic::polar_name(), "b");
        assert_eq!(Galactic::azimuth_name(), "l");

        assert_eq!(ITRF::distance_name(), "altitude");
    }

    // ── Direction inherent constructors ──

    #[test]
    fn test_icrs_direction_new() {
        let d = Direction::<ICRS>::new(120.0 * DEG, 45.0 * DEG);
        assert_eq!(d.ra(), 120.0 * DEG);
        assert_eq!(d.dec(), 45.0 * DEG);
    }

    #[test]
    fn test_horizontal_direction_new() {
        // IAU convention: polar first → new(alt, az)
        let d = Direction::<Horizontal>::new(30.0 * DEG, 180.0 * DEG);
        assert_eq!(d.alt(), 30.0 * DEG);
        assert_eq!(d.az(), 180.0 * DEG);
    }

    #[test]
    fn test_ecliptic_direction_new() {
        let d = Direction::<Ecliptic>::new(270.0 * DEG, -10.0 * DEG);
        assert_eq!(d.lon(), 270.0 * DEG);
        assert_eq!(d.lat(), -10.0 * DEG);
    }

    #[test]
    fn test_galactic_direction_new() {
        let d = Direction::<Galactic>::new(45.0 * DEG, 20.0 * DEG);
        assert_eq!(d.l(), 45.0 * DEG);
        assert_eq!(d.b(), 20.0 * DEG);
    }

    #[test]
    fn test_direction_canonicalization() {
        // RA wraps: 370° → 10°
        let d = Direction::<ICRS>::new(370.0 * DEG, 45.0 * DEG);
        assert!((d.ra().value() - 10.0).abs() < 1e-10);
        assert_eq!(d.dec(), 45.0 * DEG);

        // Dec folds: 100° → 80° (and RA shifts by 180°)
        let d = Direction::<ICRS>::new(0.0 * DEG, 100.0 * DEG);
        assert!((d.dec().value() - 80.0).abs() < 1e-10);
    }

    // ── Position inherent constructors ──

    #[derive(Debug, Copy, Clone)]
    struct TestCenter;
    impl ReferenceCenter for TestCenter {
        type Params = ();
        fn center_name() -> &'static str {
            "TestCenter"
        }
    }
    impl AffineCenter for TestCenter {}

    #[test]
    fn test_icrs_position_new() {
        let p = Position::<TestCenter, ICRS, Parsec>::new(120.0 * DEG, 45.0 * DEG, 10.0);
        assert_eq!(p.ra(), 120.0 * DEG);
        assert_eq!(p.dec(), 45.0 * DEG);
    }

    #[test]
    fn test_horizontal_position_new() {
        let p = Position::<TestCenter, Horizontal, Kilometer>::new(30.0 * DEG, 180.0 * DEG, 100.0);
        assert_eq!(p.alt(), 30.0 * DEG);
        assert_eq!(p.az(), 180.0 * DEG);
    }

    #[test]
    fn test_position_accessors_any_center() {
        // Position accessors should work for centers with non-() Params too
        #[derive(Debug, Copy, Clone)]
        struct ParamCenter;
        impl ReferenceCenter for ParamCenter {
            type Params = f64;
            fn center_name() -> &'static str {
                "ParamCenter"
            }
        }

        let p = Position::<ParamCenter, ICRS, Parsec>::new_raw_with_params(
            42.0,
            45.0 * DEG,
            120.0 * DEG,
            Quantity::<Parsec>::new(10.0),
        );
        assert_eq!(p.ra(), 120.0 * DEG);
        assert_eq!(p.dec(), 45.0 * DEG);
    }
}
