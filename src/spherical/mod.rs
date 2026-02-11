//! Spherical coordinate types.
//!
//! - [`Position<C, F, U>`]: spherical **position** (center + frame + distance)
//! - [`Direction<F>`]: spherical **direction** (frame-only, no center)

pub mod position;
pub use position::Position;

pub mod direction;
pub use direction::Direction;

// =============================================================================
// Shared Helpers
// =============================================================================

/// Canonicalize an azimuthal angle to the range `[0°, 360°)`.
#[inline]
#[allow(dead_code)]
pub(crate) fn canonicalize_azimuth(angle: qtty::Degrees) -> qtty::Degrees {
    angle.normalize()
}

/// Canonicalize a polar angle to the range `[-90°, +90°]`.
///
/// Out-of-range values are *folded* (reflected at the pole), not clamped.
/// For example, `100° → 80°` and `-100° → -80°`.
#[inline]
#[allow(dead_code)]
pub(crate) fn canonicalize_polar(angle: qtty::Degrees) -> qtty::Degrees {
    let wrapped = angle.wrap_signed(); // (-180°, 180°]
    let v = wrapped.value();
    if v > 90.0 {
        qtty::Degrees::new(180.0 - v)
    } else if v < -90.0 {
        qtty::Degrees::new(-180.0 - v)
    } else {
        wrapped
    }
}

/// Converts Cartesian unit-vector components (x, y, z) to spherical angles.
///
/// Returns `(polar, azimuth)` in degrees, canonicalized to:
/// - polar in `[-90°, +90°]`
/// - azimuth in `[0°, 360°)`
///
/// The z component is clamped to `[-1, 1]` to prevent `asin` domain errors
/// from floating-point imprecision.
#[inline]
pub(crate) fn xyz_to_polar_azimuth(x: f64, y: f64, z: f64) -> (qtty::Degrees, qtty::Degrees) {
    use qtty::Degrees;
    let z_clamped = z.clamp(-1.0, 1.0);
    let polar = Degrees::new(z_clamped.asin().to_degrees());
    let azimuth = Degrees::new(y.atan2(x).to_degrees()).normalize();
    (polar, azimuth)
}

/// Calculates the angular separation between two points given their polar and
/// azimuthal angles using the Vincenty formula on a unit sphere.
///
/// This is more numerically stable than the simpler cos-based formula.
#[inline]
pub(crate) fn angular_separation_impl(
    polar1: qtty::Degrees,
    azimuth1: qtty::Degrees,
    polar2: qtty::Degrees,
    azimuth2: qtty::Degrees,
) -> qtty::Degrees {
    use qtty::{Degree, Radian, Radians};

    let az1 = azimuth1.to::<Radian>();
    let po1 = polar1.to::<Radian>();
    let az2 = azimuth2.to::<Radian>();
    let po2 = polar2.to::<Radian>();

    let x = (po1.cos() * po2.sin()) - (po1.sin() * po2.cos() * (az2 - az1).cos());
    let y = po2.cos() * (az2 - az1).sin();
    let z = (po1.sin() * po2.sin()) + (po1.cos() * po2.cos() * (az2 - az1).cos());

    let angle_rad = (x * x + y * y).sqrt().atan2(z);
    Radians::new(angle_rad).to::<Degree>()
}
