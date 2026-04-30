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
pub fn canonicalize_azimuth(angle: qtty::angular::Degrees) -> qtty::angular::Degrees {
    angle.normalize()
}

/// Canonicalize a polar angle to the range `[-90°, +90°]`.
///
/// Out-of-range values are *folded* (reflected at the pole), not clamped.
/// For example, `100° → 80°` and `-100° → -80°`.
///
/// This folds only the polar angle. When canonicalizing a complete spherical
/// coordinate, use [`canonicalize_polar_azimuth`] so pole crossings also rotate
/// the azimuth by 180°.
#[inline]
pub fn canonicalize_polar(angle: qtty::angular::Degrees) -> qtty::angular::Degrees {
    use qtty::angular::Degrees;
    let wrapped = angle.wrap_signed(); // (-180°, 180°]
    if wrapped > Degrees::new(90.0) {
        Degrees::new(180.0) - wrapped
    } else if wrapped < Degrees::new(-90.0) {
        Degrees::new(-180.0) - wrapped
    } else {
        wrapped
    }
}

/// Canonicalize a spherical angle pair without changing the represented direction.
///
/// - `polar` is folded into `[-90°, +90°]`.
/// - `azimuth` is normalized into `[0°, 360°)`.
/// - Crossing either pole rotates the azimuth by 180° so the resulting pair
///   represents the same unit vector.
#[inline]
#[must_use]
pub fn canonicalize_polar_azimuth(
    polar: qtty::angular::Degrees,
    azimuth: qtty::angular::Degrees,
) -> (qtty::angular::Degrees, qtty::angular::Degrees) {
    use qtty::angular::Degrees;

    let wrapped = polar.wrap_signed();
    let mut azimuth = azimuth;

    let polar = if wrapped > Degrees::new(90.0) {
        azimuth += Degrees::new(180.0);
        Degrees::new(180.0) - wrapped
    } else if wrapped < Degrees::new(-90.0) {
        azimuth += Degrees::new(180.0);
        Degrees::new(-180.0) - wrapped
    } else {
        wrapped
    };

    (polar, azimuth.normalize())
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
pub(crate) fn xyz_to_polar_azimuth(
    x: f64,
    y: f64,
    z: f64,
) -> (qtty::angular::Degrees, qtty::angular::Degrees) {
    use qtty::angular::Degrees;
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
    polar1: qtty::angular::Degrees,
    azimuth1: qtty::angular::Degrees,
    polar2: qtty::angular::Degrees,
    azimuth2: qtty::angular::Degrees,
) -> qtty::angular::Degrees {
    use qtty::angular::Radians;
    use qtty::units::{Degree, Radian};

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
