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
