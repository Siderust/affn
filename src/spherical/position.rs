//! # Spherical Position
//!
//! This module defines the core spherical [`Position`] type (center + frame + distance).
//!
//! ## Mathematical Model
//!
//! A spherical position represents a point in space using:
//! - **polar (θ)**: Latitude / declination / altitude — range `[-90°, +90°]`
//! - **azimuth (φ)**: Longitude / right ascension / azimuth — range `[0°, 360°)`
//! - **distance (r)**: Radial distance from the origin
//!
//! # Type Parameters
//! - `C`: The reference center (defines the origin)
//! - `F`: The reference frame (defines axis orientation)
//! - `U`: The length unit for the distance
//!
//! ## Example
//!
//! ```rust
//! use affn::spherical::Position;
//! use affn::frames::ReferenceFrame;
//! use affn::centers::ReferenceCenter;
//! use qtty::*;
//!
//! #[derive(Debug, Copy, Clone)]
//! struct WorldFrame;
//! impl ReferenceFrame for WorldFrame {
//!     fn frame_name() -> &'static str { "WorldFrame" }
//! }
//!
//! #[derive(Debug, Copy, Clone)]
//! struct WorldOrigin;
//! impl ReferenceCenter for WorldOrigin {
//!     type Params = ();
//!     fn center_name() -> &'static str { "WorldOrigin" }
//! }
//!
//! let pos = Position::<WorldOrigin, WorldFrame, Meter>::new_raw(
//!     45.0 * DEG,  // polar
//!     30.0 * DEG,  // azimuth
//!     1.0 * M      // distance
//! );
//! ```

use crate::centers;
use crate::frames;
use qtty::*;

use std::marker::PhantomData;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "serde")]
fn is_zero_sized<T>() -> bool {
    std::mem::size_of::<T>() == 0
}

/// A spherical **position** (center + frame + distance).
///
/// This is the fundamental spherical coordinate type.
/// Spherical directions are represented separately by [`super::direction::Direction<F>`]
/// and intentionally have **no** reference center.
///
/// # Type Parameters
/// - `C`: The reference center (defines the origin)
/// - `F`: The reference frame (defines axis orientation)
/// - `U`: The length unit for the distance
///
/// # Note
///
/// `U` must be a [`LengthUnit`], not just any `Unit`. This ensures that spherical
/// positions always represent physical locations with a meaningful distance.
#[derive(Debug, Clone, Copy)]
pub struct Position<C: centers::ReferenceCenter, F: frames::ReferenceFrame, U: LengthUnit> {
    /// Polar angle (θ) - latitude, declination, or altitude, in degrees.
    pub polar: Degrees,
    /// Azimuthal angle (φ) - longitude, right ascension, or azimuth, in degrees.
    pub azimuth: Degrees,
    /// Radial distance from the origin.
    pub distance: Quantity<U>,

    center_params: C::Params,
    _frame: PhantomData<F>,
}

impl<C, F, U> Position<C, F, U>
where
    C: centers::ReferenceCenter,
    F: frames::ReferenceFrame,
    U: LengthUnit,
{
    /// Constructs a new spherical position with explicit center parameters.
    pub const fn new_raw_with_params(
        center_params: C::Params,
        polar: Degrees,
        azimuth: Degrees,
        distance: Quantity<U>,
    ) -> Self {
        Self {
            polar,
            azimuth,
            distance,
            center_params,
            _frame: PhantomData,
        }
    }

    /// Returns a reference to the center parameters.
    pub fn center_params(&self) -> &C::Params {
        &self.center_params
    }

    /// Calculates the angular separation between this position and another.
    pub fn angular_separation(&self, other: Self) -> Degrees {
        let az1 = self.azimuth.to::<Radian>();
        let po1 = self.polar.to::<Radian>();
        let az2 = other.azimuth.to::<Radian>();
        let po2 = other.polar.to::<Radian>();

        let x = (po1.cos() * po2.sin()) - (po1.sin() * po2.cos() * (az2 - az1).cos());
        let y = po2.cos() * (az2 - az1).sin();
        let z = (po1.sin() * po2.sin()) + (po1.cos() * po2.cos() * (az2 - az1).cos());

        let angle_rad = (x * x + y * y).sqrt().atan2(z);
        Radians::new(angle_rad).to::<Degree>()
    }

    /// Extracts the corresponding spherical **direction** (frame-only).
    #[must_use]
    pub fn direction(&self) -> super::direction::Direction<F> {
        super::direction::Direction::new(self.polar, self.azimuth)
    }

    /// Converts to Cartesian position.
    #[must_use]
    pub fn to_cartesian(&self) -> crate::cartesian::Position<C, F, U>
    where
        F: frames::ReferenceFrame,
    {
        let polar_rad = self.polar.to::<Radian>();
        let azimuth_rad = self.azimuth.to::<Radian>();

        let x = self.distance * azimuth_rad.cos() * polar_rad.cos();
        let y = self.distance * azimuth_rad.sin() * polar_rad.cos();
        let z = self.distance * polar_rad.sin();

        crate::cartesian::Position::<C, F, U>::new_with_params(self.center_params.clone(), x, y, z)
    }

    /// Constructs from a Cartesian position.
    #[must_use]
    pub fn from_cartesian(cart: &crate::cartesian::Position<C, F, U>) -> Self
    where
        F: frames::ReferenceFrame,
    {
        let x = cart.x().value();
        let y = cart.y().value();
        let z = cart.z().value();
        let r = cart.distance().value();

        let polar = if r.abs() < f64::EPSILON {
            Degrees::new(0.0)
        } else {
            let z_clamped = (z / r).clamp(-1.0, 1.0);
            Degrees::new(z_clamped.asin().to_degrees())
        };

        let mut azimuth = Degrees::new(y.atan2(x).to_degrees());
        if azimuth.value() < 0.0 {
            azimuth = Degrees::new(azimuth.value() + 360.0);
        }

        Self::new_raw_with_params(
            cart.center_params().clone(),
            polar,
            azimuth,
            cart.distance(),
        )
    }
}

impl<C, F, U> Position<C, F, U>
where
    C: centers::ReferenceCenter<Params = ()>,
    F: frames::ReferenceFrame,
    U: LengthUnit,
{
    /// Convenience constructor for centers with `Params = ()`.
    pub const fn new_raw(polar: Degrees, azimuth: Degrees, distance: Quantity<U>) -> Self {
        Self::new_raw_with_params((), polar, azimuth, distance)
    }

    /// The *origin* of this coordinate system (all angles 0, radius 0). AKA Null Vector.
    pub const CENTER: Self = Self::new_raw(
        Degrees::new(0.0),
        Degrees::new(0.0),
        Quantity::<U>::new(0.0),
    );
}

impl<C, F, U> Position<C, F, U>
where
    C: centers::ReferenceCenter,
    F: frames::ReferenceFrame,
    U: LengthUnit,
{
    /// Euclidean distance to another position **in the same centre & frame**.
    ///
    /// The result is expressed in the *same unit `U`* as the inputs.
    #[must_use]
    pub fn distance_to(&self, other: &Self) -> Quantity<U>
    where
        U: std::cmp::PartialEq + std::fmt::Debug,
        F: frames::ReferenceFrame,
    {
        self.to_cartesian().distance_to(&other.to_cartesian())
    }
}

impl<C, F, U> std::fmt::Display for Position<C, F, U>
where
    C: centers::ReferenceCenter,
    F: frames::ReferenceFrame,
    U: LengthUnit,
    Quantity<U>: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Center: {}, Frame: {}, θ: {:.6}, φ: {:.6}, r: {:.6}",
            C::center_name(),
            F::frame_name(),
            self.polar,
            self.azimuth,
            self.distance
        )
    }
}

// =============================================================================
// Serde Implementation with Frame-Specific Field Names
// =============================================================================

#[cfg(feature = "serde")]
mod serde_impl {
    use super::*;
    use crate::frames::SphericalNaming;
    use serde::de::{self, MapAccess, Visitor};
    use serde::ser::SerializeStruct;
    use serde::{Deserializer, Serializer};
    use std::fmt;

    impl<C, F, U> Serialize for Position<C, F, U>
    where
        C: centers::ReferenceCenter,
        C::Params: Serialize,
        F: SphericalNaming,
        U: LengthUnit,
    {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let polar_name = F::polar_name();
            let azimuth_name = F::azimuth_name();
            let distance_name = F::distance_name();
            let has_params = !is_zero_sized::<C::Params>();

            let field_count = if has_params { 4 } else { 3 };
            let mut state = serializer.serialize_struct("Position", field_count)?;
            state.serialize_field(polar_name, &self.polar)?;
            state.serialize_field(azimuth_name, &self.azimuth)?;
            state.serialize_field(distance_name, &self.distance)?;
            if has_params {
                state.serialize_field("center_params", &self.center_params)?;
            }
            state.end()
        }
    }

    impl<'de, C, F, U> Deserialize<'de> for Position<C, F, U>
    where
        C: centers::ReferenceCenter,
        C::Params: Deserialize<'de> + Default,
        F: SphericalNaming,
        U: LengthUnit,
    {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct PositionVisitor<C, F, U>(PhantomData<(C, F, U)>);

            impl<'de, C, F, U> Visitor<'de> for PositionVisitor<C, F, U>
            where
                C: centers::ReferenceCenter,
                C::Params: Deserialize<'de> + Default,
                F: SphericalNaming,
                U: LengthUnit,
            {
                type Value = Position<C, F, U>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    write!(
                        formatter,
                        "a spherical position with '{}', '{}', and '{}' fields",
                        F::polar_name(),
                        F::azimuth_name(),
                        F::distance_name()
                    )
                }

                fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
                where
                    M: MapAccess<'de>,
                {
                    let polar_name = F::polar_name();
                    let azimuth_name = F::azimuth_name();
                    let distance_name = F::distance_name();

                    let mut polar: Option<Degrees> = None;
                    let mut azimuth: Option<Degrees> = None;
                    let mut distance: Option<Quantity<U>> = None;
                    let mut center_params: Option<C::Params> = None;

                    while let Some(key) = map.next_key::<String>()? {
                        if key == polar_name {
                            if polar.is_some() {
                                return Err(de::Error::duplicate_field(polar_name));
                            }
                            polar = Some(map.next_value()?);
                        } else if key == azimuth_name {
                            if azimuth.is_some() {
                                return Err(de::Error::duplicate_field(azimuth_name));
                            }
                            azimuth = Some(map.next_value()?);
                        } else if key == distance_name {
                            if distance.is_some() {
                                return Err(de::Error::duplicate_field(distance_name));
                            }
                            distance = Some(map.next_value()?);
                        } else if key == "center_params" {
                            if center_params.is_some() {
                                return Err(de::Error::duplicate_field("center_params"));
                            }
                            center_params = Some(map.next_value()?);
                        } else {
                            // Skip unknown fields
                            let _ = map.next_value::<de::IgnoredAny>()?;
                        }
                    }

                    let polar = polar.ok_or_else(|| de::Error::missing_field(polar_name))?;
                    let azimuth = azimuth.ok_or_else(|| de::Error::missing_field(azimuth_name))?;
                    let distance =
                        distance.ok_or_else(|| de::Error::missing_field(distance_name))?;

                    // Use default for center_params if not provided and ZST
                    let center_params = center_params.unwrap_or_default();

                    Ok(Position {
                        polar,
                        azimuth,
                        distance,
                        center_params,
                        _frame: PhantomData,
                    })
                }
            }

            deserializer.deserialize_map(PositionVisitor(PhantomData))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Import the derives and traits
    use crate::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};
    use std::f64::consts::SQRT_2;

    // Define test-specific frame and center
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestFrame;
    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct TestCenter;

    #[derive(Clone, Debug, Default, PartialEq)]
    struct TestParams {
        id: i32,
    }

    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    #[center(params = TestParams)]
    struct ParamCenter;

    const EPS: f64 = 1e-6;

    #[test]
    fn test_spherical_coord_creation() {
        // new_raw(polar, azimuth, distance)
        let coord = Position::<TestCenter, TestFrame, Meter>::new_raw(
            Degrees::new(90.0),
            Degrees::new(45.0),
            1.0 * M,
        );
        assert_eq!(coord.polar.value(), 90.0);
        assert_eq!(coord.azimuth.value(), 45.0);
        assert_eq!(coord.distance.value(), 1.0);
    }

    #[test]
    fn test_spherical_coord_to_string() {
        // new_raw(polar, azimuth, distance)
        let coord = Position::<TestCenter, TestFrame, Meter>::new_raw(
            Degrees::new(60.0),
            Degrees::new(30.0),
            1000.0 * M,
        );
        let coord_string = coord.to_string();
        assert!(coord_string.contains("θ: 60"));
        assert!(coord_string.contains("φ: 30"));
        assert!(coord_string.contains("r: 1000"));
    }

    #[test]
    fn test_spherical_coord_zero_values() {
        let coord =
            Position::<TestCenter, TestFrame, Meter>::new_raw(0.0 * DEG, 0.0 * DEG, 0.0 * M);
        assert_eq!(coord.polar.value(), 0.0);
        assert_eq!(coord.azimuth.value(), 0.0);
        assert_eq!(coord.distance.value(), 0.0);
    }

    #[test]
    fn test_spherical_coord_precision() {
        // new_raw(polar, azimuth, distance)
        let coord = Position::<TestCenter, TestFrame, Meter>::new_raw(
            45.123456 * DEG,
            90.654321 * DEG,
            1234.56789 * M,
        );
        assert!((coord.polar.value() - 45.123456).abs() < 1e-6);
        assert!((coord.azimuth.value() - 90.654321).abs() < 1e-6);
        assert!((coord.distance - 1234.56789 * M).abs() < 1e-6 * M);
    }

    #[test]
    fn direction_returns_unit_vector() {
        let pos =
            Position::<TestCenter, TestFrame, Meter>::new_raw(10.0 * DEG, 20.0 * DEG, 2.5 * M);
        let dir = pos.direction();

        // Direction has implicit radius 1
        // We verify by converting to cartesian and checking the magnitude
        let cart = dir.to_cartesian();
        let magnitude = (cart.x().powi(2) + cart.y().powi(2) + cart.z().powi(2)).sqrt();
        assert!(
            (magnitude - 1.0).abs() < EPS,
            "magnitude should be 1.0, got {}",
            magnitude
        );

        // angular components are preserved
        assert!((dir.polar - 10.0 * DEG).abs() < EPS * DEG);
        assert!((dir.azimuth - 20.0 * DEG).abs() < EPS * DEG);
    }

    #[test]
    fn center_constant_is_origin() {
        let c = Position::<TestCenter, TestFrame, Meter>::CENTER;
        assert_eq!(c.polar.value(), 0.0);
        assert_eq!(c.azimuth.value(), 0.0);
        assert_eq!(c.distance.value(), 0.0);
    }

    #[test]
    fn from_degrees_matches_new_raw() {
        let a = Position::<TestCenter, TestFrame, Meter>::new_raw(45.0 * DEG, 30.0 * DEG, 3.0 * M);
        let b = Position::<TestCenter, TestFrame, Meter>::new_raw(45.0 * DEG, 30.0 * DEG, 3.0 * M);
        assert_eq!(a.polar, b.polar);
        assert_eq!(a.azimuth, b.azimuth);
        assert_eq!(a.distance, b.distance);
    }

    #[test]
    fn distance_identity_zero_and_orthogonal() {
        // identity
        let a = Position::<TestCenter, TestFrame, Meter>::new_raw(0.0 * DEG, 0.0 * DEG, 1.0 * M);
        let d0 = a.distance_to(&a);
        assert!(d0.abs().value() < EPS);

        // orthogonal points on unit sphere → chord length sqrt(2) * r
        let b = Position::<TestCenter, TestFrame, Meter>::new_raw(0.0 * DEG, 90.0 * DEG, 1.0 * M);
        let d = a.distance_to(&b);
        assert!((d.value() - SQRT_2).abs() < EPS);
    }

    #[test]
    fn position_with_params_and_center_params() {
        let params = TestParams { id: 9 };
        let pos = Position::<ParamCenter, TestFrame, Meter>::new_raw_with_params(
            params.clone(),
            5.0 * DEG,
            10.0 * DEG,
            2.0 * M,
        );
        assert_eq!(pos.center_params(), &params);
        assert!((pos.distance.value() - 2.0).abs() < EPS);
    }

    #[test]
    fn angular_separation_quarter_turn() {
        let a = Position::<TestCenter, TestFrame, Meter>::new_raw(0.0 * DEG, 0.0 * DEG, 1.0 * M);
        let b = Position::<TestCenter, TestFrame, Meter>::new_raw(0.0 * DEG, 90.0 * DEG, 1.0 * M);
        let sep = a.angular_separation(b);
        assert!((sep.value() - 90.0).abs() < EPS);
    }

    #[test]
    fn cartesian_roundtrip_and_zero_radius() {
        type CartPos = crate::cartesian::Position<TestCenter, TestFrame, Meter>;

        let cart = CartPos::new(1.0, -1.0, 0.0);
        let sph = Position::from_cartesian(&cart);
        assert!((sph.polar.value()).abs() < EPS);
        assert!((sph.azimuth.value() - 315.0).abs() < EPS);

        let back = sph.to_cartesian();
        assert!((back.x().value() - cart.x().value()).abs() < EPS);
        assert!((back.y().value() - cart.y().value()).abs() < EPS);

        let origin = CartPos::new(0.0, 0.0, 0.0);
        let sph_origin = Position::from_cartesian(&origin);
        assert!((sph_origin.polar.value()).abs() < EPS);
        assert!((sph_origin.azimuth.value()).abs() < EPS);
        assert!(sph_origin.distance.value().abs() < EPS);
    }
}
