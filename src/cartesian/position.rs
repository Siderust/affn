//! # Cartesian Position (Affine Points)
//!
//! This module defines [`Position<C, F, U>`], an **affine point** in 3D space.
//!
//! ## Mathematical Model
//!
//! A position is a point in affine space, not a vector. It represents a location
//! relative to an origin (the reference center). Key properties:
//!
//! - **Center-dependent**: Position is measured from a specific origin `C`
//! - **Frame-dependent**: The orientation is relative to a reference frame `F`
//! - **Dimensioned**: Has a length unit `U`
//!
//! ## Affine Space Operations
//!
//! Positions do **not** form a vector space. The only valid operations are:
//!
//! | Operation | Result | Meaning |
//! |-----------|--------|---------|
//! | `Position - Position` | `Displacement` | Displacement between points |
//! | `Position + Displacement` | `Position` | Translate point by displacement |
//! | `Position - Displacement` | `Position` | Translate point backwards |
//!
//! ## Forbidden Operations
//!
//! The following operations are **mathematically invalid** and do not compile:
//!
//! - `Position + Position` — Adding points has no geometric meaning
//! - `Position * scalar` — Scaling a point makes no sense without an origin
//!
//! ## Example
//!
//! ```rust
//! use affn::cartesian::{Position, Displacement};
//! use affn::centers::ReferenceCenter;
//! use affn::frames::ReferenceFrame;
//! use qtty::*;
//!
//! // Define custom center and frame (astronomy types are in downstream crates)
//! #[derive(Debug, Copy, Clone)]
//! struct MyCenter;
//! impl ReferenceCenter for MyCenter {
//!     type Params = ();
//!     fn center_name() -> &'static str { "MyCenter" }
//! }
//!
//! #[derive(Debug, Copy, Clone)]
//! struct MyFrame;
//! impl ReferenceFrame for MyFrame {
//!     fn frame_name() -> &'static str { "MyFrame" }
//! }
//!
//! // Two positions in the custom coordinate system
//! let pos1 = Position::<MyCenter, MyFrame, AstronomicalUnit>::new(1.0, 0.0, 0.0);
//! let pos2 = Position::<MyCenter, MyFrame, AstronomicalUnit>::new(1.5, 0.0, 0.0);
//!
//! // Displacement between positions
//! let displacement: Displacement<MyFrame, AstronomicalUnit> = pos2 - pos1;
//! assert!((displacement.x().value() - 0.5).abs() < 1e-12);
//!
//! // Translate pos1 by the displacement to get pos2
//! let result = pos1 + displacement;
//! assert!((result.x().value() - 1.5).abs() < 1e-12);
//! ```

use super::vector::Displacement;
use super::xyz::XYZ;
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::{LengthUnit, Quantity};

use std::marker::PhantomData;
use std::ops::{Add, Sub};

// Serde implementations in separate module
#[cfg(feature = "serde")]
#[path = "position_serde.rs"]
mod position_serde;

/// An affine point in 3D Cartesian coordinates.
///
/// Positions represent locations in space relative to a reference center (origin).
/// Unlike vectors, positions do not form a vector space.
///
/// # Type Parameters
/// - `C`: The reference center (e.g., `Heliocentric`, `Geocentric`, `Topocentric`)
/// - `F`: The reference frame (e.g., `ICRS`, `Ecliptic`, `Equatorial`)
/// - `U`: The length unit (e.g., `AstronomicalUnit`, `Kilometer`)
///
/// # Center Parameters
///
/// Some centers (like `Topocentric`) require runtime parameters stored in `C::Params`.
/// For most centers, `Params = ()` (zero overhead).
#[derive(Debug, Clone, Copy)]
pub struct Position<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit> {
    xyz: XYZ<Quantity<U>>,
    center_params: C::Params,
    _frame: PhantomData<F>,
}

// =============================================================================
// Constructors with explicit center parameters
// =============================================================================

impl<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit> Position<C, F, U> {
    /// Creates a new position with explicit center parameters.
    ///
    /// # Arguments
    /// - `center_params`: Runtime parameters for the center (e.g., `ObserverSite` for Topocentric)
    /// - `x`, `y`, `z`: Component values (converted to `Quantity<U>`)
    #[inline]
    pub fn new_with_params<T: Into<Quantity<U>>>(
        center_params: C::Params,
        x: T,
        y: T,
        z: T,
    ) -> Self {
        Self {
            xyz: XYZ::new(x.into(), y.into(), z.into()),
            center_params,
            _frame: PhantomData,
        }
    }

    /// Creates a position from internal storage with explicit center parameters.
    #[inline]
    pub(crate) fn from_xyz_with_params(center_params: C::Params, xyz: XYZ<Quantity<U>>) -> Self {
        Self {
            xyz,
            center_params,
            _frame: PhantomData,
        }
    }

    /// Creates a position from a nalgebra Vector3 with explicit center parameters.
    #[inline]
    pub fn from_vec3(center_params: C::Params, vec3: nalgebra::Vector3<Quantity<U>>) -> Self {
        Self {
            xyz: XYZ::from_vec3(vec3),
            center_params,
            _frame: PhantomData,
        }
    }

    /// Const constructor for use in const contexts.
    #[inline]
    pub const fn new_const(
        center_params: C::Params,
        x: Quantity<U>,
        y: Quantity<U>,
        z: Quantity<U>,
    ) -> Self {
        Self {
            xyz: XYZ::new(x, y, z),
            center_params,
            _frame: PhantomData,
        }
    }

    /// Returns a reference to the center parameters.
    #[inline]
    pub fn center_params(&self) -> &C::Params {
        &self.center_params
    }
}

// =============================================================================
// Convenience constructors for centers with Params = ()
// =============================================================================

impl<C, F, U> Position<C, F, U>
where
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    /// Creates a new position for centers with `Params = ()`.
    ///
    /// This is a convenience constructor that doesn't require passing `()` explicitly.
    ///
    /// # Example
    /// ```rust
    /// use affn::cartesian::Position;
    /// use affn::frames::ReferenceFrame;
    /// use affn::centers::ReferenceCenter;
    /// use qtty::*;
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct WorldFrame;
    /// impl ReferenceFrame for WorldFrame {
    ///     fn frame_name() -> &'static str { "WorldFrame" }
    /// }
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct WorldOrigin;
    /// impl ReferenceCenter for WorldOrigin {
    ///     type Params = ();
    ///     fn center_name() -> &'static str { "WorldOrigin" }
    /// }
    ///
    /// let pos = Position::<WorldOrigin, WorldFrame, Meter>::new(1.0, 0.0, 0.0);
    /// ```
    #[inline]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T, z: T) -> Self {
        Self::new_with_params((), x, y, z)
    }

    /// Creates a position from a nalgebra Vector3 for centers with `Params = ()`.
    #[inline]
    pub fn from_vec3_origin(vec3: nalgebra::Vector3<Quantity<U>>) -> Self {
        Self::from_vec3((), vec3)
    }

    /// The origin of this coordinate system (all coordinates zero).
    pub const CENTER: Self = Self::new_const(
        (),
        Quantity::<U>::new(0.0),
        Quantity::<U>::new(0.0),
        Quantity::<U>::new(0.0),
    );
}

// =============================================================================
// Component Access
// =============================================================================

impl<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit> Position<C, F, U> {
    /// Returns the x-component.
    #[inline]
    pub fn x(&self) -> Quantity<U> {
        self.xyz.x()
    }

    /// Returns the y-component.
    #[inline]
    pub fn y(&self) -> Quantity<U> {
        self.xyz.y()
    }

    /// Returns the z-component.
    #[inline]
    pub fn z(&self) -> Quantity<U> {
        self.xyz.z()
    }

    /// Returns the underlying nalgebra Vector3.
    #[inline]
    pub fn as_vec3(&self) -> &nalgebra::Vector3<Quantity<U>> {
        self.xyz.as_vec3()
    }
}

// =============================================================================
// Geometric Operations
// =============================================================================

impl<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit> Position<C, F, U> {
    /// Computes the distance from the reference center.
    #[inline]
    pub fn distance(&self) -> Quantity<U> {
        self.xyz.magnitude()
    }

    /// Computes the distance to another position in the same center and frame.
    #[inline]
    pub fn distance_to(&self, other: &Self) -> Quantity<U>
    where
        C::Params: PartialEq,
    {
        debug_assert!(
            self.center_params == other.center_params,
            "Cannot compute distance between positions with different center parameters"
        );
        (self.xyz - other.xyz).magnitude()
    }

    /// Returns the direction (unit vector) from the center to this position.
    ///
    /// Note: Directions are frame-only types (no center). This extracts the
    /// normalized direction of the position vector.
    ///
    /// Returns `None` if the position is at the origin.
    #[inline]
    pub fn direction(&self) -> Option<super::Direction<F>> {
        self.xyz
            .to_raw()
            .try_normalize()
            .map(super::Direction::from_xyz_unchecked)
    }

    /// Returns the direction, assuming non-zero distance from origin.
    ///
    /// # Panics
    /// May produce NaN if the position is at the origin.
    #[inline]
    pub fn direction_unchecked(&self) -> super::Direction<F> {
        super::Direction::from_xyz_unchecked(self.xyz.to_raw().normalize_unchecked())
    }

    /// Converts this Cartesian position to spherical coordinates.
    ///
    /// Returns a spherical position with the same center and frame,
    /// with (polar, azimuth, distance) computed from (x, y, z).
    #[must_use]
    #[inline]
    pub fn to_spherical(&self) -> crate::spherical::Position<C, F, U> {
        crate::spherical::Position::from_cartesian(self)
    }

    /// Constructs a Cartesian position from spherical coordinates.
    ///
    /// This is equivalent to `spherical_pos.to_cartesian()`.
    #[must_use]
    #[inline]
    pub fn from_spherical(sph: &crate::spherical::Position<C, F, U>) -> Self {
        sph.to_cartesian()
    }
}

// =============================================================================
// Affine Space Operations: Position - Position -> Vector
// =============================================================================

impl<C, F, U> Sub for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Displacement<F, U>;

    /// Computes the displacement vector from `other` to `self`.
    ///
    /// # Panics (debug only)
    /// Panics if the positions have different center parameters.
    #[inline]
    fn sub(self, other: Self) -> Self::Output {
        debug_assert!(
            self.center_params == other.center_params,
            "Cannot subtract positions with different center parameters"
        );
        Displacement::from_xyz(self.xyz - other.xyz)
    }
}

impl<C, F, U> Sub<&Position<C, F, U>> for &Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Displacement<F, U>;

    #[inline]
    fn sub(self, other: &Position<C, F, U>) -> Self::Output {
        debug_assert!(
            self.center_params == other.center_params,
            "Cannot subtract positions with different center parameters"
        );
        Displacement::from_xyz(self.xyz - other.xyz)
    }
}

// =============================================================================
// Affine Space Operations: Position + Vector -> Position
// =============================================================================

impl<C, F, U> Add<Displacement<F, U>> for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Self;

    /// Translates the position by a displacement vector.
    #[inline]
    fn add(self, displacement: Displacement<F, U>) -> Self::Output {
        Self::from_xyz_with_params(
            self.center_params.clone(),
            self.xyz + XYZ::from_vec3(*displacement.as_vec3()),
        )
    }
}

impl<C, F, U> Sub<Displacement<F, U>> for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Self;

    /// Translates the position backwards by a displacement vector.
    #[inline]
    fn sub(self, displacement: Displacement<F, U>) -> Self::Output {
        Self::from_xyz_with_params(
            self.center_params.clone(),
            self.xyz - XYZ::from_vec3(*displacement.as_vec3()),
        )
    }
}

// =============================================================================
// Legacy API: sub() method for backward compatibility
// =============================================================================

impl<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit> Position<C, F, U> {
    /// Computes the displacement vector from another position to this one.
    ///
    /// This is equivalent to `self - other` and returns a `Displacement<F, U>`.
    ///
    /// # Deprecated
    /// Prefer using the `-` operator: `target - observer`
    #[deprecated(note = "Use the `-` operator instead: `target - observer`.")]
    #[inline]
    pub fn sub(&self, other: &Self) -> Displacement<F, U>
    where
        C::Params: PartialEq,
    {
        debug_assert!(
            self.center_params == other.center_params,
            "Cannot subtract positions with different center parameters"
        );
        Displacement::from_xyz(self.xyz - other.xyz)
    }
}

// =============================================================================
// Display
// =============================================================================

impl<C, F, U> std::fmt::Display for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    Quantity<U>: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Center: {}, Frame: {}, X: {:.6}, Y: {:.6}, Z: {:.6}",
            C::center_name(),
            F::frame_name(),
            self.x(),
            self.y(),
            self.z()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Import the derives
    use crate::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};
    use qtty::*;

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

    type TestPos = Position<TestCenter, TestFrame, Meter>;
    type TestDisp = Displacement<TestFrame, Meter>;

    #[test]
    fn test_position_minus_position_gives_vector() {
        let a = TestPos::new(1.0, 2.0, 3.0);
        let b = TestPos::new(4.0, 5.0, 6.0);

        let displacement: TestDisp = b - a;
        assert!((displacement.x().value() - 3.0).abs() < 1e-12);
        assert!((displacement.y().value() - 3.0).abs() < 1e-12);
        assert!((displacement.z().value() - 3.0).abs() < 1e-12);
    }

    #[test]
    fn test_position_plus_vector_gives_position() {
        let pos = TestPos::new(1.0, 2.0, 3.0);
        let vec = TestDisp::new(1.0, 1.0, 1.0);

        let result: TestPos = pos + vec;
        assert!((result.x().value() - 2.0).abs() < 1e-12);
        assert!((result.y().value() - 3.0).abs() < 1e-12);
        assert!((result.z().value() - 4.0).abs() < 1e-12);
    }

    #[test]
    fn test_position_roundtrip() {
        let a = TestPos::new(1.0, 2.0, 3.0);
        let b = TestPos::new(4.0, 5.0, 6.0);

        // a + (b - a) == b
        let displacement = b - a;
        let result = a + displacement;
        assert!((result.x().value() - b.x().value()).abs() < 1e-12);
        assert!((result.y().value() - b.y().value()).abs() < 1e-12);
        assert!((result.z().value() - b.z().value()).abs() < 1e-12);
    }

    #[test]
    fn test_position_distance() {
        let pos = TestPos::new(3.0, 4.0, 0.0);
        assert!((pos.distance().value() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn test_position_direction() {
        let pos = TestPos::new(3.0, 4.0, 0.0);
        let dir = pos.direction().expect("non-zero position");
        let norm = (dir.x() * dir.x() + dir.y() * dir.y() + dir.z() * dir.z()).sqrt();
        assert!((norm - 1.0).abs() < 1e-12);
        assert!((dir.x() - 0.6).abs() < 1e-12);
        assert!((dir.y() - 0.8).abs() < 1e-12);
    }

    #[test]
    fn test_position_with_params_and_from_vec3() {
        let params = TestParams { id: 42 };
        let pos = Position::<ParamCenter, TestFrame, Meter>::new_with_params(
            params.clone(),
            1.0,
            2.0,
            3.0,
        );
        assert_eq!(pos.center_params(), &params);

        let vec3 = nalgebra::Vector3::new(1.0 * M, 2.0 * M, 3.0 * M);
        let pos_from_vec =
            Position::<ParamCenter, TestFrame, Meter>::from_vec3(params.clone(), vec3);
        assert_eq!(pos_from_vec.center_params(), &params);
        assert!((pos_from_vec.z().value() - 3.0).abs() < 1e-12);
    }

    #[test]
    fn test_position_from_vec3_origin_and_center() {
        let vec3 = nalgebra::Vector3::new(1.0 * M, 2.0 * M, 3.0 * M);
        let pos = Position::<TestCenter, TestFrame, Meter>::from_vec3_origin(vec3);
        assert!((pos.x().value() - 1.0).abs() < 1e-12);

        let origin = Position::<TestCenter, TestFrame, Meter>::CENTER;
        assert!(origin.distance().value().abs() < 1e-12);
    }

    #[test]
    fn test_position_distance_to_and_sub_methods() {
        let a = TestPos::new(0.0, 0.0, 0.0);
        let b = TestPos::new(0.0, 3.0, 4.0);
        let dist = a.distance_to(&b);
        assert!((dist.value() - 5.0).abs() < 1e-12);

        #[allow(deprecated)]
        let disp = Position::<TestCenter, TestFrame, Meter>::sub(&b, &a);
        assert!((disp.y().value() - 3.0).abs() < 1e-12);
    }

    #[test]
    fn test_position_direction_unchecked_and_sub_displacement() {
        let pos = TestPos::new(0.0, 3.0, 4.0);
        let dir = pos.direction_unchecked();
        assert!((dir.y() - 0.6).abs() < 1e-12);
        assert!((dir.z() - 0.8).abs() < 1e-12);

        let disp = TestDisp::new(1.0, 1.0, 1.0);
        let moved = pos - disp;
        assert!((moved.y().value() - 2.0).abs() < 1e-12);
    }

    #[test]
    fn test_position_spherical_roundtrip() {
        let pos = TestPos::new(1.0, 1.0, 1.0);
        let sph = pos.to_spherical();
        let back = TestPos::from_spherical(&sph);
        assert!((back.x().value() - pos.x().value()).abs() < 1e-12);
        assert!((back.y().value() - pos.y().value()).abs() < 1e-12);
        assert!((back.z().value() - pos.z().value()).abs() < 1e-12);
    }

    #[test]
    fn test_position_const_vec3_and_display() {
        let pos =
            Position::<TestCenter, TestFrame, Meter>::new_const((), 1.0 * M, 2.0 * M, 3.0 * M);
        let vec3 = pos.as_vec3();
        assert!((vec3[0].value() - 1.0).abs() < 1e-12);
        assert!((vec3[1].value() - 2.0).abs() < 1e-12);
        assert!((vec3[2].value() - 3.0).abs() < 1e-12);

        let text = pos.to_string();
        assert!(text.contains("Center: TestCenter"));
        assert!(text.contains("Frame: TestFrame"));
    }

    #[test]
    fn test_position_sub_ref_ref() {
        let a = TestPos::new(1.0, 2.0, 3.0);
        let b = TestPos::new(4.0, 6.0, 9.0);
        let displacement: TestDisp = b - a;
        assert!((displacement.x().value() - 3.0).abs() < 1e-12);
        assert!((displacement.y().value() - 4.0).abs() < 1e-12);
        assert!((displacement.z().value() - 6.0).abs() < 1e-12);
    }
}
