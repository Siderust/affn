//! 2D affine geometry primitives.
//!
//! The planar API mirrors the Cartesian 3D affine rules in two dimensions:
//! positions are affine points, vectors are free vectors, and directions are
//! normalized frame-only vectors.
//!
//! ```compile_fail
//! use affn::planar::Position;
//! use affn::prelude::*;
//! use qtty::units::Meter;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct Frame;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct Center;
//!
//! let a = Position::<Center, Frame, Meter>::new(1.0, 2.0);
//! let b = Position::<Center, Frame, Meter>::new(3.0, 4.0);
//! let _invalid = a + b;
//! ```

use core::marker::PhantomData;
use core::ops::{Add, Mul, Neg, Sub};

use crate::algebra::{Point2, Space, Vector2};
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use crate::ops::{Isometry2, Rotation2, Translation2};
use qtty::angular::Radians;
use qtty::length::LengthUnit;
use qtty::{Quantity, Unit};

#[derive(Debug, Copy, Clone)]
pub struct PlanarSpace<C: ReferenceCenter, F: ReferenceFrame>(PhantomData<(C, F)>);

impl<C: ReferenceCenter, F: ReferenceFrame> Space for PlanarSpace<C, F> {}

#[derive(Debug, Copy, Clone)]
pub struct FrameSpace<F: ReferenceFrame>(PhantomData<F>);

impl<F: ReferenceFrame> Space for FrameSpace<F> {}

/// A free vector in a 2D frame.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Vector<F: ReferenceFrame, U: Unit> {
    xy: Vector2<FrameSpace<F>, U>,
}

/// A displacement vector in a 2D frame.
pub type Displacement<F, U> = Vector<F, U>;

/// A velocity vector in a 2D frame.
pub type Velocity<F, U> = Vector<F, U>;

/// A 2D affine point relative to a center and frame.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Position<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit> {
    xy: Point2<PlanarSpace<C, F>, U>,
    center_params: C::Params,
}

/// A normalized 2D direction.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Direction<F: ReferenceFrame> {
    xy: [f64; 2],
    _frame: PhantomData<F>,
}

impl<F: ReferenceFrame, U: Unit> Vector<F, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T) -> Self {
        Self {
            xy: Vector2::new(x, y),
        }
    }

    #[inline]
    #[must_use]
    pub fn from_components(components: [Quantity<U>; 2]) -> Self {
        Self {
            xy: Vector2::from_components(components),
        }
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.xy.x()
    }

    #[inline]
    #[must_use]
    pub fn y(&self) -> Quantity<U> {
        self.xy.y()
    }

    #[inline]
    #[must_use]
    pub fn components(self) -> [Quantity<U>; 2] {
        self.xy.components()
    }

    #[inline]
    #[must_use]
    pub fn magnitude(&self) -> Quantity<U> {
        let x = self.x().value();
        let y = self.y().value();
        Quantity::new(x.hypot(y))
    }

    #[inline]
    #[must_use]
    pub fn scale(&self, factor: f64) -> Self {
        Self {
            xy: self.xy.scale(factor),
        }
    }

    #[inline]
    #[must_use]
    pub fn to_unit<U2: Unit<Dim = U::Dim>>(&self) -> Vector<F, U2> {
        Vector {
            xy: self.xy.to_unit(),
        }
    }

    #[inline]
    #[must_use]
    pub fn reinterpret_frame<F2: ReferenceFrame>(self) -> Vector<F2, U> {
        Vector::new(self.x(), self.y())
    }
}

impl<F: ReferenceFrame, U: LengthUnit> Vector<F, U> {
    #[inline]
    #[must_use]
    pub fn normalize(&self) -> Option<Direction<F>> {
        Direction::try_new(self.x().value(), self.y().value())
    }
}

impl<F: ReferenceFrame, U: Unit> Add for Vector<F, U> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            xy: self.xy + rhs.xy,
        }
    }
}

impl<F: ReferenceFrame, U: Unit> Sub for Vector<F, U> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            xy: self.xy - rhs.xy,
        }
    }
}

impl<F: ReferenceFrame, U: Unit> Neg for Vector<F, U> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self { xy: -self.xy }
    }
}

impl<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit> Position<C, F, U> {
    #[inline]
    #[must_use]
    pub fn new_with_params<T: Into<Quantity<U>>>(center_params: C::Params, x: T, y: T) -> Self {
        Self {
            xy: Point2::new(x, y),
            center_params,
        }
    }

    #[inline]
    #[must_use]
    pub fn center_params(&self) -> &C::Params {
        &self.center_params
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.xy.x()
    }

    #[inline]
    #[must_use]
    pub fn y(&self) -> Quantity<U> {
        self.xy.y()
    }

    #[inline]
    #[must_use]
    pub fn distance(&self) -> Quantity<U> {
        let x = self.x().value();
        let y = self.y().value();
        Quantity::new(x.hypot(y))
    }

    #[inline]
    #[must_use]
    pub fn to_unit<U2: LengthUnit>(&self) -> Position<C, F, U2>
    where
        C::Params: Clone,
    {
        Position::new_with_params(self.center_params.clone(), self.x().to(), self.y().to())
    }

    #[inline]
    #[must_use]
    pub fn reinterpret_frame<F2: ReferenceFrame>(self) -> Position<C, F2, U>
    where
        C::Params: Clone,
    {
        Position::new_with_params(self.center_params.clone(), self.x(), self.y())
    }
}

impl<C, F, U> Position<C, F, U>
where
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T) -> Self {
        Self::new_with_params((), x, y)
    }
}

impl<C, F, U> Sub for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Displacement<F, U>;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        assert!(
            self.center_params == rhs.center_params,
            "Cannot subtract positions with different center parameters"
        );
        Vector::from_components((self.xy - rhs.xy).components())
    }
}

impl<C, F, U> Add<Displacement<F, U>> for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Clone,
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: Displacement<F, U>) -> Self::Output {
        Self {
            xy: self.xy + Vector2::from_components(rhs.components()),
            center_params: self.center_params.clone(),
        }
    }
}

impl<C, F, U> Sub<Displacement<F, U>> for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Clone,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Displacement<F, U>) -> Self::Output {
        Self {
            xy: self.xy - Vector2::from_components(rhs.components()),
            center_params: self.center_params.clone(),
        }
    }
}

impl<F: ReferenceFrame> Direction<F> {
    #[inline]
    #[must_use]
    pub fn new(x: f64, y: f64) -> Self {
        Self::try_new(x, y).expect("Cannot create Direction from zero vector")
    }

    #[inline]
    #[must_use]
    pub fn try_new(x: f64, y: f64) -> Option<Self> {
        let mag = x.hypot(y);
        if mag < f64::MIN_POSITIVE {
            None
        } else {
            Some(Self::new_unit(x / mag, y / mag))
        }
    }

    #[inline]
    #[must_use]
    pub fn new_unit(x: f64, y: f64) -> Self {
        debug_assert!((x.hypot(y) - 1.0).abs() <= 1e-10);
        Self {
            xy: [x, y],
            _frame: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> f64 {
        self.xy[0]
    }

    #[inline]
    #[must_use]
    pub fn y(&self) -> f64 {
        self.xy[1]
    }

    #[inline]
    #[must_use]
    pub fn angle(self) -> Radians {
        Radians::new(self.y().atan2(self.x()))
    }

    #[inline]
    #[must_use]
    pub fn scale<U: LengthUnit>(&self, magnitude: Quantity<U>) -> Displacement<F, U> {
        Displacement::new(
            Quantity::new(magnitude.value() * self.x()),
            Quantity::new(magnitude.value() * self.y()),
        )
    }
}

impl<F: ReferenceFrame, U: Unit> Mul<Vector<F, U>> for Rotation2 {
    type Output = Vector<F, U>;

    #[inline]
    fn mul(self, rhs: Vector<F, U>) -> Self::Output {
        let [x, y] = self.apply_array([rhs.x().value(), rhs.y().value()]);
        Vector::new(Quantity::new(x), Quantity::new(y))
    }
}

impl<F: ReferenceFrame> Mul<Direction<F>> for Rotation2 {
    type Output = Direction<F>;

    #[inline]
    fn mul(self, rhs: Direction<F>) -> Self::Output {
        let [x, y] = self.apply_array([rhs.x(), rhs.y()]);
        Direction::new(x, y)
    }
}

impl<C, F, U> Mul<Position<C, F, U>> for Rotation2
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Clone,
{
    type Output = Position<C, F, U>;

    #[inline]
    fn mul(self, rhs: Position<C, F, U>) -> Self::Output {
        let [x, y] = self.apply_array([rhs.x().value(), rhs.y().value()]);
        Position::new_with_params(
            rhs.center_params.clone(),
            Quantity::new(x),
            Quantity::new(y),
        )
    }
}

impl<C, F, U> Mul<Position<C, F, U>> for Translation2<U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Clone,
{
    type Output = Position<C, F, U>;

    #[inline]
    fn mul(self, rhs: Position<C, F, U>) -> Self::Output {
        let [x, y] = self.apply_array([rhs.x().value(), rhs.y().value()]);
        Position::new_with_params(
            rhs.center_params.clone(),
            Quantity::new(x),
            Quantity::new(y),
        )
    }
}

impl<C, F, U> Mul<Position<C, F, U>> for Isometry2<U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Clone,
{
    type Output = Position<C, F, U>;

    #[inline]
    fn mul(self, rhs: Position<C, F, U>) -> Self::Output {
        let [x, y] = self.apply_point([rhs.x().value(), rhs.y().value()]);
        Position::new_with_params(
            rhs.center_params.clone(),
            Quantity::new(x),
            Quantity::new(y),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};
    use qtty::angular::Radians;
    use qtty::units::Meter;
    use qtty::Quantity;

    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestFrame;

    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct TestCenter;

    #[test]
    fn affine_position_ops() {
        let a = Position::<TestCenter, TestFrame, Meter>::new(1.0, 2.0);
        let b = Position::<TestCenter, TestFrame, Meter>::new(4.0, 6.0);
        let d = b - a;
        assert_eq!(d.x(), Quantity::<Meter>::new(3.0));
        assert_eq!(d.y(), Quantity::<Meter>::new(4.0));
        let c = a + d;
        assert_eq!(c.x(), Quantity::<Meter>::new(4.0));
        assert_eq!(c.y(), Quantity::<Meter>::new(6.0));
    }

    #[test]
    fn rotation_translation_isometry() {
        let p = Position::<TestCenter, TestFrame, Meter>::new(1.0, 0.0);
        let rotated = Rotation2::new(Radians::new(core::f64::consts::FRAC_PI_2)) * p;
        assert!(rotated.x().value().abs() < 1e-12);
        assert!((rotated.y().value() - 1.0).abs() < 1e-12);

        let iso = Isometry2::new(
            Rotation2::new(Radians::new(core::f64::consts::FRAC_PI_2)),
            Translation2::<Meter>::new(1.0, 2.0),
        );
        let result = iso * p;
        assert!((result.x().value() - 1.0).abs() < 1e-12);
        assert!((result.y().value() - 3.0).abs() < 1e-12);
    }

    #[test]
    fn direction_normalizes_and_scales() {
        let dir = Direction::<TestFrame>::new(3.0, 4.0);
        assert!((dir.x() - 0.6).abs() < 1e-12);
        assert!((dir.y() - 0.8).abs() < 1e-12);
        let displacement = dir.scale(Quantity::<Meter>::new(10.0));
        assert!((displacement.x().value() - 6.0).abs() < 1e-12);
        assert!((displacement.y().value() - 8.0).abs() < 1e-12);
    }

    #[test]
    fn vector_arithmetic() {
        let a = Vector::<TestFrame, Meter>::new(1.0, 2.0);
        let b = Vector::<TestFrame, Meter>::new(3.0, 4.0);
        let sum = a + b;
        assert_eq!(sum.x(), Quantity::<Meter>::new(4.0));
        assert_eq!(sum.y(), Quantity::<Meter>::new(6.0));
        let diff = b - a;
        assert_eq!(diff.x(), Quantity::<Meter>::new(2.0));
        assert_eq!(diff.y(), Quantity::<Meter>::new(2.0));
        let neg = -a;
        assert_eq!(neg.x(), Quantity::<Meter>::new(-1.0));
        assert_eq!(neg.y(), Quantity::<Meter>::new(-2.0));
    }

    #[test]
    fn vector_from_components() {
        use qtty::units::Meter;
        let qs = [Quantity::<Meter>::new(5.0), Quantity::<Meter>::new(-3.0)];
        let v = Vector::<TestFrame, Meter>::from_components(qs);
        assert_eq!(v.components()[0], Quantity::<Meter>::new(5.0));
        assert_eq!(v.components()[1], Quantity::<Meter>::new(-3.0));
    }

    #[test]
    fn vector_magnitude() {
        let v = Vector::<TestFrame, Meter>::new(3.0, 4.0);
        assert!((v.magnitude().value() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn vector_scale() {
        let v = Vector::<TestFrame, Meter>::new(1.0, 2.0);
        let scaled = v.scale(3.0);
        assert_eq!(scaled.x(), Quantity::<Meter>::new(3.0));
        assert_eq!(scaled.y(), Quantity::<Meter>::new(6.0));
    }

    #[test]
    fn vector_to_unit() {
        use qtty::units::Kilometer;
        let v = Vector::<TestFrame, Meter>::new(1000.0, 2000.0);
        let vkm: Vector<TestFrame, Kilometer> = v.to_unit();
        assert!((vkm.x().value() - 1.0).abs() < 1e-10);
        assert!((vkm.y().value() - 2.0).abs() < 1e-10);
    }

    #[test]
    fn vector_reinterpret_frame() {
        #[derive(Debug, Copy, Clone, ReferenceFrame)]
        struct OtherFrame;
        let v = Vector::<TestFrame, Meter>::new(1.0, 2.0);
        let v2: Vector<OtherFrame, Meter> = v.reinterpret_frame();
        assert_eq!(v2.x(), Quantity::<Meter>::new(1.0));
    }

    #[test]
    fn vector_normalize_zero_returns_none() {
        let v = Vector::<TestFrame, Meter>::new(0.0, 0.0);
        assert!(v.normalize().is_none());
    }

    #[test]
    fn vector_normalize_nonzero() {
        let v = Vector::<TestFrame, Meter>::new(3.0, 4.0);
        let dir = v.normalize().unwrap();
        assert!((dir.x() - 0.6).abs() < 1e-12);
        assert!((dir.y() - 0.8).abs() < 1e-12);
    }

    #[test]
    fn position_distance() {
        let p = Position::<TestCenter, TestFrame, Meter>::new(3.0, 4.0);
        assert!((p.distance().value() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn position_to_unit() {
        use qtty::units::Kilometer;
        let p = Position::<TestCenter, TestFrame, Meter>::new(1000.0, 2000.0);
        let pkm: Position<TestCenter, TestFrame, Kilometer> = p.to_unit();
        assert!((pkm.x().value() - 1.0).abs() < 1e-10);
        assert!((pkm.y().value() - 2.0).abs() < 1e-10);
    }

    #[test]
    fn position_reinterpret_frame() {
        #[derive(Debug, Copy, Clone, ReferenceFrame)]
        struct OtherFrame;
        let p = Position::<TestCenter, TestFrame, Meter>::new(1.0, 2.0);
        let p2: Position<TestCenter, OtherFrame, Meter> = p.reinterpret_frame();
        assert_eq!(p2.x(), Quantity::<Meter>::new(1.0));
    }

    #[test]
    fn position_sub_displacement() {
        let p = Position::<TestCenter, TestFrame, Meter>::new(5.0, 6.0);
        let d = Vector::<TestFrame, Meter>::new(1.0, 2.0);
        let result = p - d;
        assert_eq!(result.x(), Quantity::<Meter>::new(4.0));
        assert_eq!(result.y(), Quantity::<Meter>::new(4.0));
    }

    #[test]
    fn direction_try_new_zero_returns_none() {
        assert!(Direction::<TestFrame>::try_new(0.0, 0.0).is_none());
    }

    #[test]
    fn direction_new_unit() {
        let dir = Direction::<TestFrame>::new_unit(1.0, 0.0);
        assert_eq!(dir.x(), 1.0);
        assert_eq!(dir.y(), 0.0);
    }

    #[test]
    fn direction_angle() {
        let dir = Direction::<TestFrame>::new(1.0, 0.0);
        assert!((dir.angle().value()).abs() < 1e-12);
        let dir_up = Direction::<TestFrame>::new(0.0, 1.0);
        assert!((dir_up.angle().value() - core::f64::consts::FRAC_PI_2).abs() < 1e-12);
    }

    #[test]
    fn rotation2_mul_vector() {
        let r = Rotation2::new(Radians::new(core::f64::consts::FRAC_PI_2));
        let v = Vector::<TestFrame, Meter>::new(1.0, 0.0);
        let rv = r * v;
        assert!(rv.x().value().abs() < 1e-12);
        assert!((rv.y().value() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn rotation2_mul_direction() {
        let r = Rotation2::new(Radians::new(core::f64::consts::FRAC_PI_2));
        let d = Direction::<TestFrame>::new(1.0, 0.0);
        let rd = r * d;
        assert!(rd.x().abs() < 1e-12);
        assert!((rd.y() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn translation2_mul_position() {
        let t = Translation2::<Meter>::new(3.0, 4.0);
        let p = Position::<TestCenter, TestFrame, Meter>::new(1.0, 2.0);
        let result = t * p;
        assert_eq!(result.x(), Quantity::<Meter>::new(4.0));
        assert_eq!(result.y(), Quantity::<Meter>::new(6.0));
    }

    #[test]
    fn position_with_params() {
        #[derive(Debug, Copy, Clone, ReferenceCenter)]
        #[center(params = u32)]
        struct ParamCenter;
        let p = Position::<ParamCenter, TestFrame, Meter>::new_with_params(42u32, 1.0f64, 2.0f64);
        assert_eq!(*p.center_params(), 42u32);
    }
}
