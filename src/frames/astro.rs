// Astronomical reference frames for spherical coordinate systems.
//
// These are feature-gated behind `#[cfg(feature = "astro")]` to keep the
// core `affn` crate domain-agnostic. Enable the `astro` feature to use them.
//
// Because these types are defined in the same crate as `Direction`/`Position`,
// the derive macro can generate inherent named constructors and getters
// (e.g., `.ra()`, `.dec()`, `Direction::<ICRS>::new(ra, dec)`) without
// violating Rust's orphan rules for inherent impls.

use crate::ops::Rotation3;
use crate::DeriveReferenceFrame;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

// =============================================================================
// Equatorial frames (ra/dec)
// =============================================================================

/// International Celestial Reference **System** (ICRS).
///
/// The *system* — i.e. the abstract definition of the reference frame:
/// quasi-inertial, kinematically non-rotating, with origin at the solar-
/// system barycentre and axes fixed by the positions of distant quasars.
/// Adopted by the IAU at the XXIIIrd General Assembly (1997, Resolution B2)
/// as the fundamental celestial reference *system* replacing FK5/J2000.
///
/// `ICRS` is the *definition*; [`ICRF`] is the materialisation.
///
/// # Relationship to neighbouring frames
///
/// | Pair                       | Rotation                    | Magnitude |
/// |----------------------------|-----------------------------|-----------|
/// | `ICRS` ↔ [`ICRF`]          | exact identity              | 0         |
/// | `ICRS` ↔ [`GCRS`] (direction-only) | identity (translation only on positions) | 0 |
/// | `ICRS` ↔ [`EME2000`]       | IAU 2006 frame bias **B**   | ≈ 23 mas  |
///
/// The frame-bias rotation between `ICRS` and `EME2000` is the same matrix
/// that connects [`GCRS`] to [`EME2000`].  The bias constants and
/// transform methods live in `siderust::astro::frame_bias`.
///
/// # References
/// * IAU 1997 Resolution B2 (definition of the ICRS).
/// * IAU 2000 Resolution B1.3 (relationship to the GCRS).
/// * IERS Conventions (2010), §3.2 and §5.4.4.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ICRS;

/// International Celestial Reference **Frame** (ICRF).
///
/// The *realisation* of the [`ICRS`] via VLBI observations of extragalactic
/// radio sources.  The current realisation is **ICRF3** (IAU 2018, Resolution
/// B2), defined by 4536 sources at S/X, K and X/Ka bands.  DE440/DE441
/// planetary ephemerides are natively expressed in this realisation.
///
/// At the catalog level used by `affn`, `ICRS` and `ICRF` are **bit-identical
/// for direction purposes** — there is no rotation between them; the
/// distinction is only one of *provenance* (definition vs. realisation).
/// Keeping them as separate marker types prevents DE440 internal vectors
/// from being accidentally mixed with catalog-defined positions without an
/// explicit (no-op) conversion step.
///
/// See [`ICRF::direction_rotation_to_icrs`] (returns `Rotation3::IDENTITY`)
/// to obtain the canonical rotation programmatically.
///
/// # References
/// * Charlot et al., A&A 644 (2020) A159 — ICRF3 catalog.
/// * IAU 2018 Resolution B2.
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

/// Earth Mean Equator and Equinox of J2000.0 (EME2000).
///
/// Earth-based mean equator/equinox at the fundamental epoch J2000.0
/// (TT 2000-01-01 12:00).  Mathematically identical to [`EquatorialMeanJ2000`]
/// — both are the IAU 2006 *mean equator and equinox of J2000.0* axes that
/// the astrodynamics community labels "EME2000" and the astronomy / FK5
/// community calls "J2000 mean equator".  CCSDS Orbit Data Messages and most
/// flight-dynamics tools (STK, GMAT, …) use the `EME2000` label.
///
/// `EME2000` is kept as a distinct marker so that exchanged data preserves
/// the original frame name in public APIs and so that misuse against truly
/// barycentric/non-rotating frames is caught at compile time.
///
/// # Relationship to [`GCRS`] / [`ICRS`]
///
/// `EME2000` differs from [`GCRS`] (and from [`ICRS`] for direction purposes)
/// only by the **constant** IAU 2006 frame-bias rotation `B`, whose three
/// defining angles are
///
/// ```text
/// ξ₀  = −0.0166170″,  η₀  = −0.0068192″,  dα₀ = −0.0146″
/// ```
///
/// (IERS Conventions 2010, Table 5.2b).  The angular magnitude of `B` is
/// ≈ 23 mas (≈ 1.1 × 10⁻⁷ rad).  Because `B` is epoch-independent, no time
/// argument is needed to convert between `GCRS` and `EME2000`.  The bias
/// constants and transform methods live in `siderust::astro::frame_bias`.
///
/// # References
/// * IERS Conventions (2010), §5.4.4 and Table 5.2b.
/// * Hilton et al., Cel. Mech. Dyn. Astr. 94 (2006) 351 — IAU 2006 (P03).
/// * CCSDS 502.0-B-2, Orbit Data Messages.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EME2000;

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
/// The geocentric counterpart of the BCRS (barycentric CRS).  Its axes are
/// **kinematically non-rotating with respect to the [`ICRS`]** but its
/// origin is the centre of mass of the Earth (IAU 2000 Resolution B1.3).
///
/// # Direction vs. position semantics
///
/// * As a *direction* frame, `GCRS` and [`ICRS`] are **bit-identical**:
///   their axes coincide, the rotation between them is exactly the
///   identity, so a unit-vector pointing in `GCRS` has the same components
///   in `ICRS` (a translation between origins does not affect directions).
/// * As a *position* frame the two differ by the geocentre-to-barycentre
///   translation (≈ 1 AU scale).  This origin difference is encoded in the
///   center type, not in this frame marker.
///
/// # Relationship to [`EME2000`]
///
/// `GCRS` and [`EME2000`] (the mean equator and mean equinox of J2000.0)
/// differ by the constant **IAU 2006 frame-bias rotation** `B` of
/// magnitude ≈ 23 mas, originating from the small offset between the
/// ICRS pole / equinox and the dynamical mean pole / equinox at J2000.0.
/// The bias constants and transform methods live in `siderust::astro::frame_bias`.
///
/// # CIO-based reduction chain
///
/// In the IAU 2000/2006 framework, directions expressed in `GCRS` are
/// transformed to the terrestrial frame via the CIO-based procedure:
///
/// ```text
/// GCRS → (CIP X,Y + CIO s) → CIRS → (ERA) → TIRS → (W) → ITRS
/// ```
///
/// # References
/// * IAU 2000 Resolution B1.3 (definition of the GCRS).
/// * IERS Conventions (2010), §5.1 and §5.4.4 (frame bias).
/// * Soffel et al., AJ 126 (2003) 2687 — IAU 2000 relativity framework.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct GCRS;

// =============================================================================
// Canonical frame relationships among ICRS / ICRF / GCRS / EME2000
// =============================================================================
//
// These inherent methods expose the *direction-only* (identity) rotation that
// connects each pair.  Frame-bias methods (GCRS ↔ EME2000, ICRS ↔ EME2000)
// are domain-specific and live in `siderust::astro::frame_bias`.

impl ICRS {
    /// Direction-frame rotation from `ICRS` to [`ICRF`].
    ///
    /// At the catalog level used by `affn` the ICRS and its realisation
    /// ICRF are bit-identical: the rotation is exactly
    /// [`Rotation3::IDENTITY`].
    #[inline]
    #[must_use]
    pub fn direction_rotation_to_icrf() -> Rotation3 {
        Rotation3::IDENTITY
    }

    /// Direction-frame rotation from `ICRS` to [`GCRS`].
    ///
    /// Per IAU 2000 Resolution B1.3 the GCRS axes are kinematically
    /// non-rotating with respect to ICRS, so for *directions* the rotation
    /// is exactly [`Rotation3::IDENTITY`].  (Origin translation is encoded
    /// in the center type, not here.)
    #[inline]
    #[must_use]
    pub fn direction_rotation_to_gcrs() -> Rotation3 {
        Rotation3::IDENTITY
    }
}

impl ICRF {
    /// Direction-frame rotation from [`ICRF`] back to [`ICRS`].
    ///
    /// Exactly [`Rotation3::IDENTITY`] — the realisation and the system
    /// share axes by construction at the catalog level used here.
    #[inline]
    #[must_use]
    pub fn direction_rotation_to_icrs() -> Rotation3 {
        Rotation3::IDENTITY
    }
}

impl GCRS {
    /// Direction-frame rotation from [`GCRS`] back to [`ICRS`].
    ///
    /// Exactly [`Rotation3::IDENTITY`] (IAU 2000 Resolution B1.3): GCRS
    /// axes are kinematically non-rotating with respect to ICRS.  As
    /// *direction* frames they are bit-identical; only the spatial origin
    /// (geocentre vs. solar-system barycentre) differs, and that difference
    /// lives in the center type.
    #[inline]
    #[must_use]
    pub fn direction_rotation_to_icrs() -> Rotation3 {
        Rotation3::IDENTITY
    }
}

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

/// Mean ecliptic of J2000.0.
///
/// Based on the mean plane of Earth's orbit around the Sun at epoch J2000.0.
/// Uses ecliptic longitude and latitude.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EclipticMeanJ2000;

/// Mean ecliptic of date.
///
/// Uses the mean ecliptic plane (obliquity of date) without nutation.
/// Transformations to/from this frame are time-dependent and require a TT epoch.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EclipticOfDate;

/// Mean ecliptic of date.
///
/// Alias for [`EclipticOfDate`], provided for naming parity with
/// [`EquatorialMeanOfDate`].
pub type EclipticMeanOfDate = EclipticOfDate;

/// True ecliptic of date.
///
/// Uses the true ecliptic plane of date with nutation effects applied.
/// Ecliptic longitude is measured from the **true equinox** (precession +
/// nutation in longitude), and the obliquity used for the equator-to-ecliptic
/// tilt is the **true obliquity** (ε_A + Δε).
/// Transformations to/from this frame are time-dependent and require a TT epoch.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EclipticTrueOfDate;

/// International Terrestrial Reference Frame — **EOP-realised** Earth-fixed frame.
///
/// `ITRF` is the *physical* geocentric frame that co-rotates with the solid
/// Earth.  Its axes are realised through a network of VLBI / SLR / GNSS stations
/// and are linked to the celestial frame via the full IERS Earth Orientation
/// Parameters (polar motion **W**, Earth rotation angle **ERA**, and the
/// precession-nutation matrix **Q**).
///
/// # When to use `ITRF`
/// Use `ITRF` whenever the physical location of a point on the Earth's surface
/// matters and you intend to apply (or have already applied) the complete IERS
/// EOP reduction:
/// - Observatory geocentric coordinates derived from WGS-84 / ITRF2020.
/// - Polar-motion-corrected topocentric baselines.
///
/// # Distinction from `ECEF`
/// `ECEF` is a *mathematical* placeholder that deliberately ignores the ~10 m
/// polar-motion correction.  Coordinates labelled `ECEF` may differ from true `ITRF`
/// by up to tens of metres.  See [`ECEF`] for details.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(
    polar = "lat",
    azimuth = "lon",
    distance = "altitude",
    inherent,
    ellipsoid = "Grs80"
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ITRF;

/// Earth-Centred Earth-Fixed — **mathematical** geocentric frame (no EOP).
///
/// `ECEF` is a *generic* Earth-fixed reference that rotates with the Earth
/// (using ERA / GMST) but does **not** apply polar motion or the full IERS
/// EOP chain.  It is suitable for:
/// - First-order geodetic → topocentric conversions where sub-kilometre
///   accuracy is sufficient.
/// - Internal bookkeeping when a labelled "Earth-fixed" frame is needed
///   but a full EOP-realised solution is not yet available.
///
/// # Accuracy note
/// Omitting polar motion introduces an error of roughly **±10 m** in
/// geocentric Cartesian coordinates (up to ~30 m at solar maximum).
/// For observatory positioning at the metre level or better, use [`ITRF`]
/// coordinates with a full EOP correction.
///
/// # Distinction from `ITRF`
/// [`ITRF`] carries the full EOP realisation; `ECEF` does not.
/// A coordinate in `ECEF` is *implicitly* in a frame that coincides with
/// ITRF to first order but lacks the polar-motion rotation **W**.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(
    polar = "lat",
    azimuth = "lon",
    distance = "altitude",
    inherent,
    ellipsoid = "Wgs84"
)]
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
// Historical and operational frames (ra/dec)
// =============================================================================

/// Mean equator and mean equinox of B1950.0 (FK4 catalog reference).
///
/// The Fourth Fundamental Catalogue (FK4) used the mean equator and equinox of
/// the Besselian epoch B1950.0 as its reference frame. This frame was the
/// standard before the IAU adopted FK5/J2000 in 1976.
///
/// FK4 coordinates include the effects of elliptic terms of aberration (E-terms)
/// that are embedded in the catalog positions. When converting FK4 → FK5/ICRS,
/// these E-terms must be removed.
///
/// # References
/// * Standish, E.M. (1982). "Conversion of positions and proper motions from
///   B1950.0 to the IAU system at J2000.0", A&A, 115, 20-22.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct FK4B1950;

/// True Equator, Mean Equinox (TEME) frame.
///
/// An Earth-centered inertial frame used operationally for SGP4/SDP4
/// two-line element (TLE) propagation. The pole is the true celestial pole
/// (CIP, including nutation), but the origin of right ascension is the
/// **mean** equinox of date (no nutation in longitude applied to the equinox).
///
/// TEME differs from TOD (True of Date) by the equation of the equinoxes:
/// ```text
/// TEME → TOD: Rz(equation_of_equinoxes)
/// ```
///
/// # References
/// * Vallado, D.A. et al. (2006). "Revisiting Spacetrack Report No. 3",
///   AIAA/AAS Astrodynamics Specialist Conference, AIAA 2006-6753.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "dec", azimuth = "ra", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TEME;

// =============================================================================
// Planetary body-fixed frames (lat/lon/radius)
// =============================================================================

/// Mercury IAU body-fixed frame.
///
/// Planetocentric frame rotating with Mercury's solid body.
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MercuryFixed;

/// Venus IAU body-fixed frame.
///
/// Planetocentric frame rotating with Venus (retrograde rotation).
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct VenusFixed;

/// Mars IAU body-fixed frame.
///
/// Planetocentric frame rotating with Mars, the standard cartographic
/// reference used by NASA/ESA missions.
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MarsFixed;

/// Moon principal axes (selenocentric) frame.
///
/// A body-fixed frame aligned with the Moon's principal moments of inertia.
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MoonPrincipalAxes;

/// Jupiter System III body-fixed frame.
///
/// Defined by Jupiter's magnetic field rotation period (9h 55m 29.711s).
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct JupiterSystemIII;

/// Saturn IAU body-fixed frame.
///
/// Planetocentric frame rotating with Saturn's magnetic field (System III).
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SaturnFixed;

/// Uranus IAU body-fixed frame.
///
/// Planetocentric frame rotating with Uranus (extreme ~97.8° axial tilt,
/// retrograde rotation in IAU convention).
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct UranusFixed;

/// Neptune IAU body-fixed frame.
///
/// Planetocentric frame rotating with Neptune's magnetic field.
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct NeptuneFixed;

/// Pluto IAU body-fixed frame.
///
/// Planetocentric frame rotating with Pluto (retrograde rotation).
/// Uses latitude/longitude/radius spherical naming.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default, DeriveReferenceFrame)]
#[frame(polar = "lat", azimuth = "lon", distance = "radius", inherent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct PlutoFixed;

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::centers::{AffineCenter, ReferenceCenter};
    use crate::frames::{ReferenceFrame, SphericalNaming};
    use crate::spherical::{Direction, Position};
    #[allow(unused_imports)]
    use qtty::angular::{Degrees, Radians};
    #[allow(unused_imports)]
    use qtty::length::{Kilometers, Meters};
    use qtty::units::{Kilometer, Parsec};
    use qtty::Quantity;
    use qtty::DEG;
    #[test]
    fn test_frame_names() {
        assert_eq!(ICRS::frame_name(), "ICRS");
        assert_eq!(ICRF::frame_name(), "ICRF");
        assert_eq!(EME2000::frame_name(), "EME2000");
        assert_eq!(Horizontal::frame_name(), "Horizontal");
        assert_eq!(EclipticMeanJ2000::frame_name(), "EclipticMeanJ2000");
        assert_eq!(EclipticOfDate::frame_name(), "EclipticOfDate");
        assert_eq!(EclipticTrueOfDate::frame_name(), "EclipticTrueOfDate");
        assert_eq!(EclipticMeanOfDate::frame_name(), "EclipticOfDate");
        assert_eq!(Galactic::frame_name(), "Galactic");
        assert_eq!(ITRF::frame_name(), "ITRF");
        assert_eq!(ECEF::frame_name(), "ECEF");
        assert_eq!(FK4B1950::frame_name(), "FK4B1950");
        assert_eq!(TEME::frame_name(), "TEME");

        // Planetary body-fixed
        assert_eq!(MercuryFixed::frame_name(), "MercuryFixed");
        assert_eq!(VenusFixed::frame_name(), "VenusFixed");
        assert_eq!(MarsFixed::frame_name(), "MarsFixed");
        assert_eq!(MoonPrincipalAxes::frame_name(), "MoonPrincipalAxes");
        assert_eq!(JupiterSystemIII::frame_name(), "JupiterSystemIII");
        assert_eq!(SaturnFixed::frame_name(), "SaturnFixed");
        assert_eq!(UranusFixed::frame_name(), "UranusFixed");
        assert_eq!(NeptuneFixed::frame_name(), "NeptuneFixed");
        assert_eq!(PlutoFixed::frame_name(), "PlutoFixed");
    }

    #[test]
    fn test_spherical_naming() {
        assert_eq!(ICRS::polar_name(), "dec");
        assert_eq!(ICRS::azimuth_name(), "ra");
        assert_eq!(EME2000::polar_name(), "dec");
        assert_eq!(EME2000::azimuth_name(), "ra");

        assert_eq!(Horizontal::polar_name(), "alt");
        assert_eq!(Horizontal::azimuth_name(), "az");

        assert_eq!(EclipticMeanJ2000::polar_name(), "lat");
        assert_eq!(EclipticMeanJ2000::azimuth_name(), "lon");
        assert_eq!(EclipticOfDate::polar_name(), "lat");
        assert_eq!(EclipticOfDate::azimuth_name(), "lon");
        assert_eq!(EclipticTrueOfDate::polar_name(), "lat");
        assert_eq!(EclipticTrueOfDate::azimuth_name(), "lon");

        assert_eq!(Galactic::polar_name(), "b");
        assert_eq!(Galactic::azimuth_name(), "l");

        assert_eq!(ITRF::distance_name(), "altitude");

        // Planetary body-fixed: all use lat/lon/radius
        assert_eq!(MercuryFixed::polar_name(), "lat");
        assert_eq!(MercuryFixed::azimuth_name(), "lon");
        assert_eq!(MercuryFixed::distance_name(), "radius");

        assert_eq!(MarsFixed::polar_name(), "lat");
        assert_eq!(MarsFixed::azimuth_name(), "lon");
        assert_eq!(MarsFixed::distance_name(), "radius");
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
        let d = Direction::<EclipticMeanJ2000>::new(270.0 * DEG, -10.0 * DEG);
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

        let p = Position::<ParamCenter, ICRS, Parsec>::new_unchecked_with_params(
            42.0,
            45.0 * DEG,
            120.0 * DEG,
            Quantity::<Parsec>::new(10.0),
        );
        assert_eq!(p.ra(), 120.0 * DEG);
        assert_eq!(p.dec(), 45.0 * DEG);
    }
}
