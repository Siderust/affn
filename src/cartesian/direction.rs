//! # Cartesian Direction (Unit Vectors)
//!
//! This module defines [`Direction<F>`], a **dimensionless unit vector** representing
//! orientation in 3D space.
//!
//! ## Mathematical Model
//!
//! A direction is a unit-length vector representing pure orientation without magnitude:
//!
//! - **Frame-dependent**: Orientation is relative to a reference frame `F`
//! - **Center-independent**: Directions are translation-invariant (free vectors)
//! - **Dimensionless**: No length unit; magnitude is always 1
//!
//! ## Key Properties
//!
//! 1. **Immutable normalization**: All constructors produce unit vectors
//! 2. **No translation**: Directions cannot be "moved" to a different origin
//! 3. **Rotation-only transforms**: Frame transformations are the only valid spatial ops
//!
//! ## Supported Operations
//!
//! | Operation | Result | Meaning |
//! |-----------|--------|---------|
//! | `Direction * Length` | `Vector` | Scale direction to displacement |
//! | `normalize(Vector)` | `Direction` | Extract orientation from displacement |
//! | `Position.direction()` | `Direction` | Unit vector from center to position |
//!
//! ## Forbidden Operations (do not compile)
//!
//! - `Direction + Direction` — Adding unit vectors is geometrically invalid
//! - `Direction + Vector` — Translating a direction is meaningless
//! - Center transformations on Direction — Directions have no center
//!
//! ## Example
//!
//! ```rust
//! use affn::cartesian::Direction;
//! use affn::frames::ReferenceFrame;
//!
//! #[derive(Debug, Copy, Clone)]
//! struct WorldFrame;
//! impl ReferenceFrame for WorldFrame {
//!     fn frame_name() -> &'static str { "WorldFrame" }
//! }
//!
//! // Create a normalized direction
//! let dir = Direction::<WorldFrame>::new(1.0, 2.0, 2.0);
//! assert!((dir.x() - 1.0/3.0).abs() < 1e-12);
//! assert!((dir.y() - 2.0/3.0).abs() < 1e-12);
//! assert!((dir.z() - 2.0/3.0).abs() < 1e-12);
//!
//! // Scale to create a Vector
//! use qtty::*;
//! let vec = dir.scale(10.0 * M);
//! ```

use super::vector::Displacement;
use super::xyz::XYZ;
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::{LengthUnit, Quantity};

use std::marker::PhantomData;
use std::ops::Mul;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A unit vector representing orientation in 3D space.
///
/// Directions are frame-dependent but center-independent (free vectors).
/// The internal storage is a `Vector3<f64>` with magnitude 1 (dimensionless).
///
/// # Type Parameters
/// - `F`: The reference frame (e.g., `ICRS`, `Ecliptic`, `Equatorial`)
///
/// # Invariants
///
/// All public constructors ensure the direction is normalized. For unchecked
/// construction, use [`from_xyz_unchecked`](Self::from_xyz_unchecked).
///
/// # Zero-Cost Abstraction
///
/// This type is `#[repr(transparent)]` over `XYZ<f64>`, ensuring no runtime
/// overhead compared to raw `Vector3<f64>`.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(serialize = "F: ReferenceFrame", deserialize = "F: ReferenceFrame"))
)]
#[repr(transparent)]
pub struct Direction<F: ReferenceFrame> {
    #[cfg_attr(feature = "serde", serde(flatten))]
    storage: DirectionStorage<F>,
}

/// Internal storage combining XYZ and frame marker.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(serialize = "F: ReferenceFrame", deserialize = "F: ReferenceFrame"))
)]
struct DirectionStorage<F: ReferenceFrame> {
    xyz: XYZ<f64>,
    #[cfg_attr(feature = "serde", serde(skip))]
    _frame: PhantomData<F>,
}

// =============================================================================
// Constructors (Normalizing)
// =============================================================================

impl<F: ReferenceFrame> Direction<F> {
    /// Creates a direction from components, normalizing to unit length.
    ///
    /// # Panics
    /// Panics if the input vector is zero (cannot normalize).
    ///
    /// # Example
    /// ```rust
    /// use affn::cartesian::Direction;
    /// use affn::frames::ReferenceFrame;
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct WorldFrame;
    /// impl ReferenceFrame for WorldFrame {
    ///     fn frame_name() -> &'static str { "WorldFrame" }
    /// }
    ///
    /// let dir = Direction::<WorldFrame>::new(3.0, 4.0, 0.0);
    /// assert!((dir.x() - 0.6).abs() < 1e-12);
    /// assert!((dir.y() - 0.8).abs() < 1e-12);
    /// ```
    #[inline]
    pub fn new(x: f64, y: f64, z: f64) -> Self {
        Self::try_new(x, y, z).expect("Cannot create Direction from zero vector")
    }

    /// Attempts to create a direction, returning `None` if the input is zero.
    #[inline]
    pub fn try_new(x: f64, y: f64, z: f64) -> Option<Self> {
        XYZ::new(x, y, z)
            .try_normalize()
            .map(Self::from_xyz_unchecked)
    }

    /// Creates a direction from components (alias for `new`).
    ///
    /// Provided for API symmetry with earlier versions.
    #[inline]
    pub fn normalize(x: f64, y: f64, z: f64) -> Self {
        Self::new(x, y, z)
    }

    /// Creates a direction from a nalgebra Vector3, normalizing.
    #[inline]
    pub fn from_vec3(vec: nalgebra::Vector3<f64>) -> Self {
        Self::new(vec.x, vec.y, vec.z)
    }
}

// =============================================================================
// Unchecked Constructors (for internal use)
// =============================================================================

impl<F: ReferenceFrame> Direction<F> {
    /// Creates a direction from pre-normalized XYZ storage.
    ///
    /// # Safety
    /// The caller must ensure `xyz` is already a unit vector (magnitude ≈ 1).
    /// No normalization is performed.
    #[inline]
    pub(crate) fn from_xyz_unchecked(xyz: XYZ<f64>) -> Self {
        Self {
            storage: DirectionStorage {
                xyz,
                _frame: PhantomData,
            },
        }
    }

    /// Creates a direction from raw components without normalization.
    ///
    /// # Safety
    /// The caller must ensure the components form a unit vector.
    #[inline]
    pub fn new_unchecked(x: f64, y: f64, z: f64) -> Self {
        Self::from_xyz_unchecked(XYZ::new(x, y, z))
    }
}

// =============================================================================
// Component Access
// =============================================================================

impl<F: ReferenceFrame> Direction<F> {
    /// Returns the x-component.
    #[inline]
    pub fn x(&self) -> f64 {
        self.storage.xyz.x()
    }

    /// Returns the y-component.
    #[inline]
    pub fn y(&self) -> f64 {
        self.storage.xyz.y()
    }

    /// Returns the z-component.
    #[inline]
    pub fn z(&self) -> f64 {
        self.storage.xyz.z()
    }

    /// Returns the underlying nalgebra Vector3.
    #[inline]
    pub fn as_vec3(&self) -> nalgebra::Vector3<f64> {
        *self.storage.xyz.as_vec3()
    }
}

// =============================================================================
// Scaling: Direction * Length -> Vector
// =============================================================================

impl<F: ReferenceFrame> Direction<F> {
    /// Scales the direction by a length to produce a displacement vector.
    ///
    /// # Example
    /// ```rust
    /// use affn::cartesian::Direction;
    /// use affn::frames::ReferenceFrame;
    /// use qtty::*;
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct WorldFrame;
    /// impl ReferenceFrame for WorldFrame {
    ///     fn frame_name() -> &'static str { "WorldFrame" }
    /// }
    ///
    /// let dir = Direction::<WorldFrame>::new(1.0, 0.0, 0.0);
    /// let vec = dir.scale(5.0 * M);
    /// assert!((vec.x().value() - 5.0).abs() < 1e-12);
    /// ```
    #[inline]
    pub fn scale<U: LengthUnit>(&self, magnitude: Quantity<U>) -> Displacement<F, U> {
        Displacement::new(
            magnitude * self.x(),
            magnitude * self.y(),
            magnitude * self.z(),
        )
    }

    /// Creates a position at the given distance from the origin in this direction.
    ///
    /// For centers with `Params = ()`, this is a convenience method.
    #[inline]
    pub fn position<C, U>(&self, magnitude: Quantity<U>) -> super::Position<C, F, U>
    where
        C: ReferenceCenter<Params = ()>,
        U: LengthUnit,
    {
        super::Position::new(
            magnitude * self.x(),
            magnitude * self.y(),
            magnitude * self.z(),
        )
    }

    /// Creates a position with explicit center parameters.
    #[inline]
    pub fn position_with_params<C, U>(
        &self,
        center_params: C::Params,
        magnitude: Quantity<U>,
    ) -> super::Position<C, F, U>
    where
        C: ReferenceCenter,
        U: LengthUnit,
    {
        super::Position::new_with_params(
            center_params,
            magnitude * self.x(),
            magnitude * self.y(),
            magnitude * self.z(),
        )
    }
}

// =============================================================================
// Operator: Direction * Quantity<U> -> Vector
// =============================================================================

impl<F: ReferenceFrame, U: LengthUnit> Mul<Quantity<U>> for Direction<F> {
    type Output = Displacement<F, U>;

    #[inline]
    fn mul(self, magnitude: Quantity<U>) -> Self::Output {
        self.scale(magnitude)
    }
}

impl<F: ReferenceFrame, U: LengthUnit> Mul<Direction<F>> for Quantity<U> {
    type Output = Displacement<F, U>;

    #[inline]
    fn mul(self, dir: Direction<F>) -> Self::Output {
        dir.scale(self)
    }
}

// =============================================================================
// Geometric Operations
// =============================================================================

impl<F: ReferenceFrame> Direction<F> {
    /// Computes the dot product with another direction.
    ///
    /// Returns cosine of the angle between directions (range: -1 to 1).
    #[inline]
    pub fn dot(&self, other: &Self) -> f64 {
        self.storage.xyz.dot(&other.storage.xyz)
    }

    /// Computes the cross product with another direction.
    ///
    /// The result is normalized if non-zero (perpendicular directions).
    #[inline]
    pub fn cross(&self, other: &Self) -> Option<Self> {
        self.storage
            .xyz
            .cross(&other.storage.xyz)
            .try_normalize()
            .map(Self::from_xyz_unchecked)
    }

    /// Negates the direction (points in opposite direction).
    #[inline]
    pub fn negate(&self) -> Self {
        Self::from_xyz_unchecked(self.storage.xyz.neg())
    }

    /// Returns the angle between this direction and another, in radians.
    #[inline]
    pub fn angle_to(&self, other: &Self) -> f64 {
        // Clamp to handle floating-point errors at extremes
        self.dot(other).clamp(-1.0, 1.0).acos()
    }
}

// =============================================================================
// Spherical Conversion
// =============================================================================

impl<F: ReferenceFrame> Direction<F> {
    /// Converts this Cartesian direction to spherical coordinates.
    ///
    /// Returns a spherical direction with polar (latitude) and azimuth (longitude)
    /// angles in degrees. Angles are canonicalized to:
    /// - polar in `[-90°, +90°]`
    /// - azimuth in `[0°, 360°)`
    pub fn to_spherical(&self) -> crate::spherical::Direction<F> {
        use qtty::Degrees;

        let x = self.x();
        let y = self.y();
        let z = self.z();

        // Clamp z to prevent asin domain errors from floating-point imprecision
        let z_clamped = z.clamp(-1.0, 1.0);
        let polar = Degrees::new(z_clamped.asin().to_degrees());
        let azimuth = Degrees::new(y.atan2(x).to_degrees());

        // Use new() to canonicalize angles (azimuth from atan2 may be negative)
        crate::spherical::Direction::<F>::new(polar, azimuth)
    }
}

// =============================================================================
// Display
// =============================================================================

impl<F: ReferenceFrame> Direction<F> {
    /// Returns a formatted string representation.
    pub fn display(&self) -> String {
        format!(
            "Frame: {}, X: {:.6}, Y: {:.6}, Z: {:.6}",
            F::frame_name(),
            self.x(),
            self.y(),
            self.z()
        )
    }
}

impl<F: ReferenceFrame> std::fmt::Display for Direction<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Frame: {}, X: {:.6}, Y: {:.6}, Z: {:.6}",
            F::frame_name(),
            self.x(),
            self.y(),
            self.z()
        )
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    // Import the derive
    use crate::DeriveReferenceCenter as ReferenceCenter;
    use crate::DeriveReferenceFrame as ReferenceFrame;
    use qtty::*;

    // Define test-specific frame
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestFrame;
    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct TestCenter;

    #[derive(Clone, Debug, Default, PartialEq)]
    struct TestParams {
        tag: i32,
    }

    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    #[center(params = TestParams)]
    struct ParamCenter;

    #[test]
    fn test_direction_normalization() {
        let dir = Direction::<TestFrame>::new(3.0, 4.0, 0.0);
        let norm = (dir.x() * dir.x() + dir.y() * dir.y() + dir.z() * dir.z()).sqrt();
        assert!((norm - 1.0).abs() < 1e-12);
        assert!((dir.x() - 0.6).abs() < 1e-12);
        assert!((dir.y() - 0.8).abs() < 1e-12);
    }

    #[test]
    fn test_direction_scale() {
        let dir = Direction::<TestFrame>::new(1.0, 0.0, 0.0);
        let vec = dir.scale(Quantity::<Meter>::new(5.0));
        assert!((vec.x().value() - 5.0).abs() < 1e-12);
        assert!(vec.y().value().abs() < 1e-12);
        assert!(vec.z().value().abs() < 1e-12);
    }

    #[test]
    fn test_direction_dot_product() {
        let a = Direction::<TestFrame>::new(1.0, 0.0, 0.0);
        let b = Direction::<TestFrame>::new(0.0, 1.0, 0.0);
        // Perpendicular directions have dot product 0
        assert!(a.dot(&b).abs() < 1e-12);

        // Same direction has dot product 1
        assert!((a.dot(&a) - 1.0).abs() < 1e-12);

        // Opposite directions have dot product -1
        assert!((a.dot(&a.negate()) + 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_direction_cross_product() {
        let x = Direction::<TestFrame>::new(1.0, 0.0, 0.0);
        let y = Direction::<TestFrame>::new(0.0, 1.0, 0.0);
        let z = x.cross(&y).expect("perpendicular directions");
        assert!(z.x().abs() < 1e-12);
        assert!(z.y().abs() < 1e-12);
        assert!((z.z() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_direction_try_new_zero() {
        assert!(Direction::<TestFrame>::try_new(0.0, 0.0, 0.0).is_none());
    }

    #[test]
    fn test_direction_angle() {
        let a = Direction::<TestFrame>::new(1.0, 0.0, 0.0);
        let b = Direction::<TestFrame>::new(0.0, 1.0, 0.0);
        let angle = a.angle_to(&b);
        assert!((angle - std::f64::consts::FRAC_PI_2).abs() < 1e-12);
    }

    #[test]
    fn test_direction_helpers_and_accessors() {
        let dir = Direction::<TestFrame>::normalize(0.0, 3.0, 4.0);
        let vec3 = dir.as_vec3();
        assert!((vec3.x - 0.0).abs() < 1e-12);
        assert!((vec3.y - 0.6).abs() < 1e-12);
        assert!((vec3.z - 0.8).abs() < 1e-12);

        let from_vec3 = Direction::<TestFrame>::from_vec3(nalgebra::Vector3::new(0.0, 3.0, 4.0));
        assert!((from_vec3.y() - 0.6).abs() < 1e-12);
        assert!((from_vec3.z() - 0.8).abs() < 1e-12);

        let unchecked = Direction::<TestFrame>::new_unchecked(1.0, 0.0, 0.0);
        assert!((unchecked.x() - 1.0).abs() < 1e-12);
        assert!(unchecked.y().abs() < 1e-12);

        let spherical = unchecked.to_spherical();
        assert!((spherical.polar.value()).abs() < 1e-12);
        assert!((spherical.azimuth.value()).abs() < 1e-12);
    }

    #[test]
    fn test_direction_position_helpers() {
        let dir = Direction::<TestFrame>::new(1.0, 0.0, 0.0);
        let pos = dir.position::<TestCenter, Meter>(2.0 * M);
        assert!((pos.x().value() - 2.0).abs() < 1e-12);
        assert!(pos.y().value().abs() < 1e-12);

        let params = TestParams { tag: 7 };
        let pos_params = dir.position_with_params::<ParamCenter, Meter>(params.clone(), 3.0 * M);
        assert_eq!(pos_params.center_params(), &params);
        assert!((pos_params.x().value() - 3.0).abs() < 1e-12);
    }

    #[test]
    fn test_direction_scaling_operator_left() {
        let dir = Direction::<TestFrame>::new(0.0, 1.0, 0.0);
        let disp: Displacement<TestFrame, Meter> = 4.0 * M * dir;
        assert!((disp.y().value() - 4.0).abs() < 1e-12);
        assert!(disp.x().value().abs() < 1e-12);
    }

    #[test]
    fn test_direction_display() {
        let dir = Direction::<TestFrame>::new(1.0, 0.0, 0.0);
        let text = dir.display();
        assert!(text.contains("Frame: TestFrame"));
        assert!(text.contains("X: 1.000000"));
    }
}
