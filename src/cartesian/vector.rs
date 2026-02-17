//! # Cartesian Free Vector
//!
//! This module defines [`Vector<F, U>`], a **free vector** in 3D Cartesian space.
//!
//! ## Mathematical Model
//!
//! A free vector represents a directed magnitude in space. It is:
//! - **Frame-dependent**: The orientation is relative to a reference frame `F`
//! - **Center-independent**: Free vectors are translation-invariant
//! - **Dimensioned**: Has a unit `U` (length, velocity, acceleration, etc.)
//!
//! Free vectors form a vector space and support:
//! - Addition: `Vector + Vector -> Vector`
//! - Subtraction: `Vector - Vector -> Vector`
//! - Scalar multiplication: `Vector * f64 -> Vector`
//! - Normalization (for length units): `normalize(Vector) -> Option<Direction>`
//!
//! ## Semantic Type Aliases
//!
//! This module provides semantic aliases for clarity:
//! - [`Displacement<F, U>`] — displacement vector with length unit
//! - [`Velocity<F, U>`] — velocity vector with velocity unit
//!
//! ## Example
//!
//! ```rust
//! use affn::cartesian::{Vector, Displacement, Velocity};
//! use affn::frames::ReferenceFrame;
//! use qtty::*;
//!
//! // Define a custom frame (astronomy frames are defined in downstream crates)
//! #[derive(Debug, Copy, Clone)]
//! struct MyFrame;
//! impl ReferenceFrame for MyFrame {
//!     fn frame_name() -> &'static str { "MyFrame" }
//! }
//!
//! // Displacement with length unit
//! let displacement = Displacement::<MyFrame, AstronomicalUnit>::new(1.0, 2.0, 3.0);
//!
//! // Velocity with velocity unit
//! type AuPerDay = Per<AstronomicalUnit, Day>;
//! let velocity = Velocity::<MyFrame, AuPerDay>::new(0.01, 0.02, 0.0);
//!
//! // Both are just Vector<F, U> with different units
//! let v: Vector<MyFrame, AuPerDay> = velocity;
//! ```

use super::xyz::XYZ;
use crate::frames::ReferenceFrame;
use qtty::{LengthUnit, Quantity, Unit};

use std::marker::PhantomData;
use std::ops::{Add, Neg, Sub};

// Serde implementations in separate module
#[cfg(feature = "serde")]
#[path = "vector_serde.rs"]
mod vector_serde;

/// A free vector in 3D Cartesian coordinates.
///
/// Free vectors are frame-dependent but center-independent. They represent
/// directed magnitudes (displacement, velocity, acceleration, etc.) in space.
///
/// # Type Parameters
/// - `F`: The reference frame (e.g., `ICRS`, `EclipticMeanJ2000`, `Equatorial`)
/// - `U`: The unit (e.g., `AstronomicalUnit`, `Per<Kilometer, Second>`)
///
/// # Zero-Cost Abstraction
///
/// This type uses `#[repr(transparent)]` over the internal storage,
/// ensuring no runtime overhead compared to raw `Vector3<Quantity<U>>`.
#[derive(Debug, Clone, Copy)]
pub struct Vector<F: ReferenceFrame, U: Unit> {
    xyz: XYZ<Quantity<U>>,
    _frame: PhantomData<F>,
}

// =============================================================================
// Constructors
// =============================================================================

impl<F: ReferenceFrame, U: Unit> Vector<F, U> {
    /// Creates a new vector from component values.
    ///
    /// # Arguments
    /// - `x`, `y`, `z`: Component values (converted to `Quantity<U>`)
    #[inline]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T, z: T) -> Self {
        Self {
            xyz: XYZ::new(x.into(), y.into(), z.into()),
            _frame: PhantomData,
        }
    }

    /// Creates a vector from a nalgebra Vector3.
    #[inline]
    pub fn from_vec3(vec3: nalgebra::Vector3<Quantity<U>>) -> Self {
        Self {
            xyz: XYZ::from_vec3(vec3),
            _frame: PhantomData,
        }
    }

    /// Creates a vector from the internal XYZ storage.
    #[inline]
    pub(crate) fn from_xyz(xyz: XYZ<Quantity<U>>) -> Self {
        Self {
            xyz,
            _frame: PhantomData,
        }
    }

    /// The zero vector.
    pub const ZERO: Self = Self {
        xyz: XYZ::new(
            Quantity::<U>::new(0.0),
            Quantity::<U>::new(0.0),
            Quantity::<U>::new(0.0),
        ),
        _frame: PhantomData,
    };
}

// =============================================================================
// Component Access
// =============================================================================

impl<F: ReferenceFrame, U: Unit> Vector<F, U> {
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

    /// Converts this vector to another unit of the same dimension.
    ///
    /// The frame is preserved and each component is converted independently
    /// via `qtty::Quantity::to`.
    #[inline]
    pub fn to_unit<U2: Unit<Dim = U::Dim>>(&self) -> Vector<F, U2> {
        Vector::<F, U2>::new(
            self.x().to::<U2>(),
            self.y().to::<U2>(),
            self.z().to::<U2>(),
        )
    }
}

// =============================================================================
// Vector Space Operations (for all units)
// =============================================================================

impl<F: ReferenceFrame, U: Unit> Vector<F, U> {
    /// Computes the Euclidean magnitude of the vector.
    #[inline]
    pub fn magnitude(&self) -> Quantity<U> {
        self.xyz.magnitude()
    }

    /// Computes the squared magnitude (avoids sqrt, useful for comparisons).
    #[inline]
    pub fn magnitude_squared(&self) -> f64 {
        self.xyz.magnitude_squared()
    }

    /// Scales the vector by a scalar factor.
    #[inline]
    pub fn scale(&self, factor: f64) -> Self {
        Self::from_xyz(XYZ::from_raw(self.xyz.to_raw().scale(factor)))
    }

    /// Computes the dot product with another vector (returns dimensionless f64).
    ///
    /// Note: For proper dimensional analysis, the result would be U²,
    /// but we return the raw f64 value for convenience.
    #[inline]
    pub fn dot(&self, other: &Self) -> f64 {
        self.xyz.to_raw().dot(&other.xyz.to_raw())
    }

    /// Computes the cross product with another vector.
    #[inline]
    pub fn cross(&self, other: &Self) -> Self {
        Self::from_xyz(XYZ::from_raw(self.xyz.to_raw().cross(&other.xyz.to_raw())))
    }

    /// Returns the negation of this vector.
    #[inline]
    pub fn negate(&self) -> Self {
        Self::from_xyz(-self.xyz)
    }
}

// =============================================================================
// Length-Specific Operations (only for LengthUnit)
// =============================================================================

impl<F: ReferenceFrame, U: LengthUnit> Vector<F, U> {
    /// Normalizes this vector to a unit direction.
    ///
    /// Returns `None` if the vector has zero (or near-zero) magnitude.
    ///
    /// # Example
    /// ```rust
    /// use affn::cartesian::Displacement;
    /// use affn::frames::ReferenceFrame;
    /// use qtty::*;
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct MyFrame;
    /// impl ReferenceFrame for MyFrame {
    ///     fn frame_name() -> &'static str { "MyFrame" }
    /// }
    ///
    /// let v = Displacement::<MyFrame, AstronomicalUnit>::new(3.0, 4.0, 0.0);
    /// let dir = v.normalize().expect("non-zero vector");
    /// // dir is now a unit Direction<MyFrame>
    /// ```
    #[inline]
    pub fn normalize(&self) -> Option<super::Direction<F>> {
        self.xyz
            .to_raw()
            .try_normalize()
            .map(super::Direction::from_xyz_unchecked)
    }

    /// Returns a unit direction, assuming non-zero magnitude.
    ///
    /// # Panics
    /// May produce NaN if the vector has zero magnitude.
    #[inline]
    pub fn normalize_unchecked(&self) -> super::Direction<F> {
        super::Direction::from_xyz_unchecked(self.xyz.to_raw().normalize_unchecked())
    }
}

// =============================================================================
// Operator Implementations
// =============================================================================

impl<F: ReferenceFrame, U: Unit> Add for Vector<F, U> {
    type Output = Self;

    /// Vector + Vector -> Vector
    #[inline]
    fn add(self, other: Self) -> Self::Output {
        Self::from_xyz(self.xyz + other.xyz)
    }
}

impl<F: ReferenceFrame, U: Unit> Sub for Vector<F, U> {
    type Output = Self;

    /// Vector - Vector -> Vector
    #[inline]
    fn sub(self, other: Self) -> Self::Output {
        Self::from_xyz(self.xyz - other.xyz)
    }
}

impl<F: ReferenceFrame, U: Unit> Neg for Vector<F, U> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.negate()
    }
}

// =============================================================================
// PartialEq
// =============================================================================

impl<F: ReferenceFrame, U: Unit> PartialEq for Vector<F, U> {
    fn eq(&self, other: &Self) -> bool {
        self.xyz == other.xyz
    }
}

// =============================================================================
// Display
// =============================================================================

impl<F: ReferenceFrame, U: Unit> std::fmt::Display for Vector<F, U>
where
    Quantity<U>: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vector<{}> X: {:.6}, Y: {:.6}, Z: {:.6}",
            F::frame_name(),
            self.x(),
            self.y(),
            self.z()
        )
    }
}

// =============================================================================
// Type Aliases
// =============================================================================

/// A displacement vector (free vector with length unit).
///
/// This is a semantic alias for [`Vector<F, U>`] where `U` is a length unit.
/// Displacements represent directed distances in space.
pub type Displacement<F, U> = Vector<F, U>;

/// A velocity vector (free vector with velocity unit).
///
/// This is a semantic alias for [`Vector<F, U>`] where `U` is a velocity unit.
/// Velocities represent rates of change of position.
pub type Velocity<F, U> = Vector<F, U>;

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    // Import the derive
    use crate::DeriveReferenceFrame as ReferenceFrame;
    use qtty::{AstronomicalUnit, Day, Kilometer, Meter, Per, Quantity};

    // Define a test frame using the macro
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestFrame;

    type DispAu = Displacement<TestFrame, AstronomicalUnit>;
    type AuPerDay = Per<AstronomicalUnit, Day>;
    type VelAuDay = Velocity<TestFrame, AuPerDay>;

    #[test]
    fn test_vector_add_sub() {
        let a = DispAu::new(1.0, 2.0, 3.0);
        let b = DispAu::new(4.0, 5.0, 6.0);

        let sum = a + b;
        assert!((sum.x().value() - 5.0).abs() < 1e-12);
        assert!((sum.y().value() - 7.0).abs() < 1e-12);
        assert!((sum.z().value() - 9.0).abs() < 1e-12);

        let diff = b - a;
        assert!((diff.x().value() - 3.0).abs() < 1e-12);
        assert!((diff.y().value() - 3.0).abs() < 1e-12);
        assert!((diff.z().value() - 3.0).abs() < 1e-12);
    }

    #[test]
    fn test_vector_magnitude() {
        let v = DispAu::new(3.0, 4.0, 0.0);
        assert!((v.magnitude().value() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn test_displacement_normalize() {
        let v = DispAu::new(3.0, 4.0, 0.0);
        let dir = v.normalize().expect("non-zero displacement");
        let norm = (dir.x() * dir.x() + dir.y() * dir.y() + dir.z() * dir.z()).sqrt();
        assert!((norm - 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_zero_displacement_normalize() {
        let zero = DispAu::ZERO;
        assert!(zero.normalize().is_none());
    }

    #[test]
    fn test_velocity_add_sub() {
        let v1 = VelAuDay::new(
            Quantity::<AuPerDay>::new(1.0),
            Quantity::<AuPerDay>::new(2.0),
            Quantity::<AuPerDay>::new(3.0),
        );
        let v2 = VelAuDay::new(
            Quantity::<AuPerDay>::new(0.5),
            Quantity::<AuPerDay>::new(1.0),
            Quantity::<AuPerDay>::new(1.5),
        );

        let sum = v1 + v2;
        assert!((sum.x().value() - 1.5).abs() < 1e-12);
        assert!((sum.y().value() - 3.0).abs() < 1e-12);
        assert!((sum.z().value() - 4.5).abs() < 1e-12);

        let diff = v1 - v2;
        assert!((diff.x().value() - 0.5).abs() < 1e-12);
        assert!((diff.y().value() - 1.0).abs() < 1e-12);
        assert!((diff.z().value() - 1.5).abs() < 1e-12);
    }

    #[test]
    fn test_velocity_magnitude() {
        let v = VelAuDay::new(
            Quantity::<AuPerDay>::new(3.0),
            Quantity::<AuPerDay>::new(4.0),
            Quantity::<AuPerDay>::new(0.0),
        );
        assert!((v.magnitude().value() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn test_vector_misc_ops() {
        let v = DispAu::new(1.0, 2.0, 3.0);
        let scaled = v.scale(2.0);
        assert_eq!(scaled, DispAu::new(2.0, 4.0, 6.0));

        let neg = v.negate();
        assert!((neg.x().value() + 1.0).abs() < 1e-12);
        assert!((neg.y().value() + 2.0).abs() < 1e-12);

        let dot = v.dot(&DispAu::new(0.0, 1.0, 0.0));
        assert!((dot - 2.0).abs() < 1e-12);

        let cross = v.cross(&DispAu::new(0.0, 1.0, 0.0));
        assert!((cross.x().value() + 3.0).abs() < 1e-12);
        assert!(cross.y().value().abs() < 1e-12);
        assert!((cross.z().value() - 1.0).abs() < 1e-12);

        let magnitude_sq = v.magnitude_squared();
        assert!((magnitude_sq - 14.0).abs() < 1e-12);

        let from_vec3 = DispAu::from_vec3(nalgebra::Vector3::new(
            Quantity::<AstronomicalUnit>::new(1.0),
            Quantity::<AstronomicalUnit>::new(2.0),
            Quantity::<AstronomicalUnit>::new(3.0),
        ));
        assert_eq!(from_vec3, v);

        let dir = v.normalize_unchecked();
        let norm = (dir.x() * dir.x() + dir.y() * dir.y() + dir.z() * dir.z()).sqrt();
        assert!((norm - 1.0).abs() < 1e-12);

        let neg_op = -v;
        assert_eq!(neg_op, neg);
    }

    #[test]
    fn test_vector_display_and_accessors() {
        let v = Displacement::<TestFrame, Meter>::new(1.0, 2.0, 3.0);
        let vec3 = v.as_vec3();
        assert!((vec3[0].value() - 1.0).abs() < 1e-12);
        assert!((vec3[1].value() - 2.0).abs() < 1e-12);
        assert!((vec3[2].value() - 3.0).abs() < 1e-12);

        let text = v.to_string();
        assert!(text.contains("Vector<TestFrame>"));
    }

    #[test]
    fn test_vector_to_unit_roundtrip() {
        let v_au = DispAu::new(1.0, -2.0, 0.5);
        let v_km: Displacement<TestFrame, Kilometer> = v_au.to_unit();
        let back: DispAu = v_km.to_unit();

        assert!((back.x().value() - v_au.x().value()).abs() < 1e-12);
        assert!((back.y().value() - v_au.y().value()).abs() < 1e-12);
        assert!((back.z().value() - v_au.z().value()).abs() < 1e-12);
    }

    #[test]
    fn test_velocity_to_unit_roundtrip() {
        type KmPerDay = Per<Kilometer, Day>;

        let v_au_day = VelAuDay::new(
            Quantity::<AuPerDay>::new(0.01),
            Quantity::<AuPerDay>::new(-0.02),
            Quantity::<AuPerDay>::new(0.03),
        );
        let v_km_day: Velocity<TestFrame, KmPerDay> = v_au_day.to_unit();
        let back: VelAuDay = v_km_day.to_unit();

        assert!((back.x().value() - v_au_day.x().value()).abs() < 1e-12);
        assert!((back.y().value() - v_au_day.y().value()).abs() < 1e-12);
        assert!((back.z().value() - v_au_day.z().value()).abs() < 1e-12);
    }
}
