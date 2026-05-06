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
//! use qtty::units::{Meter, Second};
//! use qtty::Per;
//!
//! // Define a custom frame (astronomy frames are defined in downstream crates)
//! #[derive(Debug, Copy, Clone)]
//! struct MyFrame;
//! impl ReferenceFrame for MyFrame {
//!     fn frame_name() -> &'static str { "MyFrame" }
//! }
//!
//! // Displacement with length unit
//! let _displacement = Displacement::<MyFrame, Meter>::new(1.0, 2.0, 3.0);
//!
//! // Velocity with velocity unit
//! type MPerS = Per<Meter, Second>;
//! let velocity = Velocity::<MyFrame, MPerS>::new(0.01, 0.02, 0.0);
//!
//! // Both are just Vector<F, U> with different units
//! let _v: Vector<MyFrame, MPerS> = velocity;
//! ```

use super::xyz::XYZ;
use crate::frames::ReferenceFrame;
use qtty::length::LengthUnit;
use qtty::{Quantity, Unit, UnitMul};

use std::marker::PhantomData;
use std::ops::{Add, Neg, Sub};

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
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct Vector<F: ReferenceFrame, U: Unit> {
    pub(in crate::cartesian) xyz: XYZ<Quantity<U>>,
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

    /// Reinterprets this vector as belonging to a different reference frame.
    ///
    /// This is a **zero-cost** operation: the components are preserved
    /// unchanged; only the compile-time frame tag `F` is replaced by `F2`.
    ///
    /// Use after applying a mathematical rotation whose result still carries
    /// the original frame tag.
    #[inline]
    pub fn reinterpret_frame<F2: ReferenceFrame>(self) -> Vector<F2, U> {
        Vector::new(self.x(), self.y(), self.z())
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

    /// Scales the vector by a scalar factor.
    #[inline]
    pub fn scale(&self, factor: f64) -> Self {
        Self::from_xyz(XYZ::from_raw(self.xyz.to_raw().scale(factor)))
    }

    /// Returns the negation of this vector.
    #[inline]
    pub fn negate(&self) -> Self {
        Self::from_xyz(-self.xyz)
    }
}

// =============================================================================
// Squared-unit operations (require U: UnitMul<U>)
// =============================================================================

impl<F: ReferenceFrame, U: Unit + UnitMul<U>> Vector<F, U> {
    /// Computes the squared magnitude (avoids sqrt, useful for comparisons).
    ///
    /// Returns a quantity in the squared unit `U·U` (e.g. `m·m` for a
    /// length vector), produced by the [`UnitMul`] machinery in `qtty`.
    #[inline]
    pub fn magnitude_squared(&self) -> Quantity<<U as UnitMul<U>>::Output> {
        self.xyz.magnitude_squared()
    }

    /// Computes the dot product with another vector.
    ///
    /// Returns a quantity in the squared unit `U·U`.
    #[inline]
    pub fn dot(&self, other: &Self) -> Quantity<<U as UnitMul<U>>::Output> {
        let s = self.xyz.to_raw().dot(&other.xyz.to_raw());
        Quantity::new(s)
    }

    /// Computes the cross product with another vector.
    ///
    /// Returns a vector whose components are in the squared unit `U·U`.
    #[inline]
    pub fn cross(&self, other: &Self) -> Vector<F, <U as UnitMul<U>>::Output> {
        let raw = self.xyz.to_raw().cross(&other.xyz.to_raw());
        Vector::<F, <U as UnitMul<U>>::Output>::new(
            Quantity::new(raw.x()),
            Quantity::new(raw.y()),
            Quantity::new(raw.z()),
        )
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
    /// use qtty::units::Meter;
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct MyFrame;
    /// impl ReferenceFrame for MyFrame {
    ///     fn frame_name() -> &'static str { "MyFrame" }
    /// }
    ///
    /// let v = Displacement::<MyFrame, Meter>::new(3.0, 4.0, 0.0);
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

forward_ref_binop! { impl[F: ReferenceFrame, U: Unit] Add, add for Vector<F, U>, Vector<F, U> }

impl<F: ReferenceFrame, U: Unit> Sub for Vector<F, U> {
    type Output = Self;

    /// Vector - Vector -> Vector
    #[inline]
    fn sub(self, other: Self) -> Self::Output {
        Self::from_xyz(self.xyz - other.xyz)
    }
}

forward_ref_binop! { impl[F: ReferenceFrame, U: Unit] Sub, sub for Vector<F, U>, Vector<F, U> }

impl<F: ReferenceFrame, U: Unit> Neg for Vector<F, U> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.negate()
    }
}

forward_ref_unop! { impl[F: ReferenceFrame, U: Unit] Neg, neg for Vector<F, U> }

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

impl_quantity_fmt_triplet! {
    impl[F, U] for Vector<F, U>
    where {
        F: ReferenceFrame,
        U: Unit,
    },
    fmt_each: { Quantity<U>, },
    |this, f, FmtOne| {
        write!(f, "Vector<{}> X: ", F::frame_name())?;
        FmtOne::fmt(&this.x(), f)?;
        write!(f, ", Y: ")?;
        FmtOne::fmt(&this.y(), f)?;
        write!(f, ", Z: ")?;
        FmtOne::fmt(&this.z(), f)
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
    use qtty::units::{Kilometer, Meter, Second};
    use qtty::{Per, Quantity};

    // Define a test frame using the macro
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestFrame;

    type DispM = Displacement<TestFrame, Meter>;
    type MPerS = Per<Meter, Second>;
    type VelMPerS = Velocity<TestFrame, MPerS>;

    #[test]
    fn test_vector_add_sub() {
        let a = DispM::new(1.0, 2.0, 3.0);
        let b = DispM::new(4.0, 5.0, 6.0);

        let sum = a + b;
        assert!((sum.x().value() - 5.0).abs() < 1e-12);
        assert!((sum.y().value() - 7.0).abs() < 1e-12);
        assert!((sum.z().value() - 9.0).abs() < 1e-12);

        let diff = b - a;
        assert!((diff.x().value() - 3.0).abs() < 1e-12);
        assert!((diff.y().value() - 3.0).abs() < 1e-12);
        assert!((diff.z().value() - 3.0).abs() < 1e-12);
    }

    /// Smoke test: every reference combination of a representative binary
    /// operator (`Vector + Vector`) and unary operator (`-Vector`) must
    /// produce identical results to the by-value form.
    #[test]
    #[allow(clippy::op_ref)]
    fn ref_ops_uniformity_smoke() {
        let a = DispM::new(1.0, 2.0, 3.0);
        let b = DispM::new(4.0, 5.0, 6.0);
        let expected = DispM::new(5.0, 7.0, 9.0);

        let by_value = a + b;
        let lhs_ref = &a + b;
        let rhs_ref = a + &b;
        let both_ref = &a + &b;

        let check = |got: DispM| {
            assert!((got.x().value() - expected.x().value()).abs() < 1e-12);
            assert!((got.y().value() - expected.y().value()).abs() < 1e-12);
            assert!((got.z().value() - expected.z().value()).abs() < 1e-12);
        };
        check(by_value);
        check(lhs_ref);
        check(rhs_ref);
        check(both_ref);

        // Unary Neg: by-value and &T must agree.
        let n_value = -a;
        let n_ref = -&a;
        assert!((n_value.x().value() - n_ref.x().value()).abs() < 1e-12);
        assert!((n_value.y().value() - n_ref.y().value()).abs() < 1e-12);
        assert!((n_value.z().value() - n_ref.z().value()).abs() < 1e-12);
    }

    #[test]
    fn test_vector_magnitude() {
        let v = DispM::new(3.0, 4.0, 0.0);
        assert!((v.magnitude().value() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn test_displacement_normalize() {
        let v = DispM::new(3.0, 4.0, 0.0);
        let dir = v.normalize().expect("non-zero displacement");
        let norm = (dir.x() * dir.x() + dir.y() * dir.y() + dir.z() * dir.z()).sqrt();
        assert!((norm - 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_zero_displacement_normalize() {
        let zero = DispM::ZERO;
        assert!(zero.normalize().is_none());
    }

    #[test]
    fn test_velocity_add_sub() {
        let v1 = VelMPerS::new(
            Quantity::<MPerS>::new(1.0),
            Quantity::<MPerS>::new(2.0),
            Quantity::<MPerS>::new(3.0),
        );
        let v2 = VelMPerS::new(
            Quantity::<MPerS>::new(0.5),
            Quantity::<MPerS>::new(1.0),
            Quantity::<MPerS>::new(1.5),
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
        let v = VelMPerS::new(
            Quantity::<MPerS>::new(3.0),
            Quantity::<MPerS>::new(4.0),
            Quantity::<MPerS>::new(0.0),
        );
        assert!((v.magnitude().value() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn test_vector_misc_ops() {
        let v = DispM::new(1.0, 2.0, 3.0);
        let scaled = v.scale(2.0);
        assert_eq!(scaled, DispM::new(2.0, 4.0, 6.0));

        let neg = v.negate();
        assert!((neg.x().value() + 1.0).abs() < 1e-12);
        assert!((neg.y().value() + 2.0).abs() < 1e-12);

        let dot = v.dot(&DispM::new(0.0, 1.0, 0.0));
        assert!((dot.value() - 2.0).abs() < 1e-12);

        let cross = v.cross(&DispM::new(0.0, 1.0, 0.0));
        assert!((cross.x().value() + 3.0).abs() < 1e-12);
        assert!(cross.y().value().abs() < 1e-12);
        assert!((cross.z().value() - 1.0).abs() < 1e-12);

        let magnitude_sq = v.magnitude_squared();
        assert!((magnitude_sq.value() - 14.0).abs() < 1e-12);

        let from_vec3 = DispM::from_vec3(nalgebra::Vector3::new(
            Quantity::<Meter>::new(1.0),
            Quantity::<Meter>::new(2.0),
            Quantity::<Meter>::new(3.0),
        ));
        assert_eq!(from_vec3, v);

        let dir = v.normalize_unchecked();
        let norm = (dir.x() * dir.x() + dir.y() * dir.y() + dir.z() * dir.z()).sqrt();
        assert!((norm - 1.0).abs() < 1e-12);

        let neg_op = -v;
        assert_eq!(neg_op, neg);
    }

    #[test]
    fn test_typed_dot_cross_magnitude_squared() {
        // Typed dot/cross/magnitude_squared return Quantity<Prod<U, U>>.
        use qtty::Prod;

        let v = Displacement::<TestFrame, Meter>::new(1.0, 0.0, 0.0);
        let w = Displacement::<TestFrame, Meter>::new(1.0, 0.0, 0.0);

        // Type assertion: dot returns Quantity<Prod<Meter, Meter>>
        let d: Quantity<Prod<Meter, Meter>> = v.dot(&w);
        assert!((d.value() - 1.0).abs() < 1e-12);

        // magnitude_squared also returns Quantity<Prod<Meter, Meter>>
        let m2: Quantity<Prod<Meter, Meter>> = v.magnitude_squared();
        assert!((m2.value() - 1.0).abs() < 1e-12);

        // sqrt round-trips back to Quantity<Meter>
        let m: Quantity<Meter> = m2.sqrt();
        assert!((m.value() - 1.0).abs() < 1e-12);

        // cross returns Vector<F, Prod<Meter, Meter>>
        let a = Displacement::<TestFrame, Meter>::new(1.0, 0.0, 0.0);
        let b = Displacement::<TestFrame, Meter>::new(0.0, 1.0, 0.0);
        let c: Vector<TestFrame, Prod<Meter, Meter>> = a.cross(&b);
        assert!((c.x().value()).abs() < 1e-12);
        assert!((c.y().value()).abs() < 1e-12);
        assert!((c.z().value() - 1.0).abs() < 1e-12);
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

        let text_prec = format!("{:.1}", v);
        let expected_x_prec = format!("{:.1}", v.x());
        assert!(text_prec.contains(&format!("X: {expected_x_prec}")));

        let text_exp = format!("{:.2e}", v);
        let expected_y_exp = format!("{:.2e}", v.y());
        assert!(text_exp.contains(&format!("Y: {expected_y_exp}")));
    }

    #[test]
    fn test_vector_to_unit_roundtrip() {
        let v_m = DispM::new(1.0, -2.0, 0.5);
        let v_km: Displacement<TestFrame, Kilometer> = v_m.to_unit();
        let back: DispM = v_km.to_unit();

        assert!((back.x().value() - v_m.x().value()).abs() < 1e-12);
        assert!((back.y().value() - v_m.y().value()).abs() < 1e-12);
        assert!((back.z().value() - v_m.z().value()).abs() < 1e-12);
    }

    #[test]
    fn test_velocity_to_unit_roundtrip() {
        type KmPerS = Per<Kilometer, Second>;

        let v_m_s = VelMPerS::new(
            Quantity::<MPerS>::new(0.01),
            Quantity::<MPerS>::new(-0.02),
            Quantity::<MPerS>::new(0.03),
        );
        let v_km_s: Velocity<TestFrame, KmPerS> = v_m_s.to_unit();
        let back: VelMPerS = v_km_s.to_unit();

        assert!((back.x().value() - v_m_s.x().value()).abs() < 1e-12);
        assert!((back.y().value() - v_m_s.y().value()).abs() < 1e-12);
        assert!((back.z().value() - v_m_s.z().value()).abs() < 1e-12);
    }

    #[test]
    fn vector_has_xyz_layout() {
        assert_eq!(
            core::mem::size_of::<DispM>(),
            core::mem::size_of::<XYZ<Quantity<Meter>>>()
        );
        assert_eq!(
            core::mem::align_of::<DispM>(),
            core::mem::align_of::<XYZ<Quantity<Meter>>>()
        );
    }
}
