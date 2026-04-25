//! Dimension-generic affine algebra primitives.
//!
//! This module contains the domain-neutral algebra underneath coordinate
//! systems and one-dimensional axes such as time. It deliberately has no
//! astronomy, frame, center, or civil-time vocabulary.
//!
//! ```compile_fail
//! use affn::algebra::{Point1, Space};
//! use qtty::units::Meter;
//!
//! #[derive(Debug, Copy, Clone)]
//! struct Line;
//! impl Space for Line {}
//!
//! let a = Point1::<Line, Meter>::new(1.0);
//! let b = Point1::<Line, Meter>::new(2.0);
//! let _invalid = a + b;
//! ```

use core::fmt::Debug;
use core::marker::PhantomData;
use core::ops::{Add, Neg, Sub};

use qtty::{Quantity, Unit};

/// Marker trait for an affine space or coordinate axis.
///
/// Implement this for zero-sized domain marker types. The marker carries the
/// type-level identity of a space; it has no runtime state.
pub trait Space: Copy + Clone + Debug {}

impl Space for () {}

/// A free vector in an affine space.
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct Vector<Sp: Space, U: Unit, const N: usize> {
    components: [Quantity<U>; N],
    _space: PhantomData<Sp>,
}

/// An affine point in an affine space.
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct Point<Sp: Space, U: Unit, const N: usize> {
    coordinates: [Quantity<U>; N],
    _space: PhantomData<Sp>,
}

/// One-dimensional affine point.
pub type Point1<Sp, U> = Point<Sp, U, 1>;
/// Two-dimensional affine point.
pub type Point2<Sp, U> = Point<Sp, U, 2>;
/// Three-dimensional affine point.
pub type Point3<Sp, U> = Point<Sp, U, 3>;

/// One-dimensional free vector.
pub type Vector1<Sp, U> = Vector<Sp, U, 1>;
/// Two-dimensional free vector.
pub type Vector2<Sp, U> = Vector<Sp, U, 2>;
/// Three-dimensional free vector.
pub type Vector3<Sp, U> = Vector<Sp, U, 3>;

#[inline]
fn scaled<U: Unit>(value: Quantity<U>, factor: f64) -> Quantity<U> {
    Quantity::new(value.value() * factor)
}

impl<Sp: Space, U: Unit, const N: usize> Vector<Sp, U, N> {
    /// Creates a vector from typed components.
    #[inline]
    #[must_use]
    pub const fn from_components(components: [Quantity<U>; N]) -> Self {
        Self {
            components,
            _space: PhantomData,
        }
    }

    /// Creates a vector from raw scalar values in unit `U`.
    #[inline]
    #[must_use]
    pub fn from_values(values: [f64; N]) -> Self {
        Self::from_components(values.map(Quantity::new))
    }

    /// Returns the typed components.
    #[inline]
    #[must_use]
    pub const fn components(self) -> [Quantity<U>; N] {
        self.components
    }

    /// Returns a reference to the typed components.
    #[inline]
    #[must_use]
    pub const fn as_components(&self) -> &[Quantity<U>; N] {
        &self.components
    }

    /// Returns one component by index.
    #[inline]
    #[must_use]
    pub fn component(&self, index: usize) -> Quantity<U> {
        self.components[index]
    }

    /// Scales this vector by a dimensionless scalar.
    #[inline]
    #[must_use]
    pub fn scale(self, factor: f64) -> Self {
        Self::from_components(self.components.map(|c| scaled(c, factor)))
    }

    /// Converts this vector to another unit of the same dimension.
    #[inline]
    #[must_use]
    pub fn to_unit<U2: Unit<Dim = U::Dim>>(self) -> Vector<Sp, U2, N> {
        Vector::from_components(self.components.map(|c| c.to::<U2>()))
    }
}

impl<Sp: Space, U: Unit, const N: usize> PartialEq for Vector<Sp, U, N> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.components == other.components
    }
}

impl<Sp: Space, U: Unit, const N: usize> Point<Sp, U, N> {
    /// Creates a point from typed coordinates.
    #[inline]
    #[must_use]
    pub const fn from_coordinates(coordinates: [Quantity<U>; N]) -> Self {
        Self {
            coordinates,
            _space: PhantomData,
        }
    }

    /// Creates a point from raw scalar values in unit `U`.
    #[inline]
    #[must_use]
    pub fn from_values(values: [f64; N]) -> Self {
        Self::from_coordinates(values.map(Quantity::new))
    }

    /// Returns the typed coordinates.
    #[inline]
    #[must_use]
    pub const fn coordinates(self) -> [Quantity<U>; N] {
        self.coordinates
    }

    /// Returns a reference to the typed coordinates.
    #[inline]
    #[must_use]
    pub const fn as_coordinates(&self) -> &[Quantity<U>; N] {
        &self.coordinates
    }

    /// Returns one coordinate by index.
    #[inline]
    #[must_use]
    pub fn coordinate(&self, index: usize) -> Quantity<U> {
        self.coordinates[index]
    }

    /// Converts this point to another unit of the same dimension.
    #[inline]
    #[must_use]
    pub fn to_unit<U2: Unit<Dim = U::Dim>>(self) -> Point<Sp, U2, N> {
        Point::from_coordinates(self.coordinates.map(|c| c.to::<U2>()))
    }
}

impl<Sp: Space, U: Unit, const N: usize> PartialEq for Point<Sp, U, N> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.coordinates == other.coordinates
    }
}

impl<Sp: Space, U: Unit> Vector1<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T) -> Self {
        Self::from_components([x.into()])
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.components[0]
    }
}

impl<Sp: Space, U: Unit> Point1<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T) -> Self {
        Self::from_coordinates([x.into()])
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.coordinates[0]
    }
}

impl<Sp: Space, U: Unit> Vector2<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T) -> Self {
        Self::from_components([x.into(), y.into()])
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.components[0]
    }

    #[inline]
    #[must_use]
    pub fn y(&self) -> Quantity<U> {
        self.components[1]
    }
}

impl<Sp: Space, U: Unit> Point2<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T) -> Self {
        Self::from_coordinates([x.into(), y.into()])
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.coordinates[0]
    }

    #[inline]
    #[must_use]
    pub fn y(&self) -> Quantity<U> {
        self.coordinates[1]
    }
}

impl<Sp: Space, U: Unit> Vector3<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T, z: T) -> Self {
        Self::from_components([x.into(), y.into(), z.into()])
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.components[0]
    }

    #[inline]
    #[must_use]
    pub fn y(&self) -> Quantity<U> {
        self.components[1]
    }

    #[inline]
    #[must_use]
    pub fn z(&self) -> Quantity<U> {
        self.components[2]
    }
}

impl<Sp: Space, U: Unit> Point3<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>>(x: T, y: T, z: T) -> Self {
        Self::from_coordinates([x.into(), y.into(), z.into()])
    }

    #[inline]
    #[must_use]
    pub fn x(&self) -> Quantity<U> {
        self.coordinates[0]
    }

    #[inline]
    #[must_use]
    pub fn y(&self) -> Quantity<U> {
        self.coordinates[1]
    }

    #[inline]
    #[must_use]
    pub fn z(&self) -> Quantity<U> {
        self.coordinates[2]
    }
}

impl<Sp: Space, U: Unit, const N: usize> Add for Vector<Sp, U, N> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self::from_components(core::array::from_fn(|i| self.components[i] + rhs.components[i]))
    }
}

impl<Sp: Space, U: Unit, const N: usize> Sub for Vector<Sp, U, N> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self::from_components(core::array::from_fn(|i| self.components[i] - rhs.components[i]))
    }
}

impl<Sp: Space, U: Unit, const N: usize> Neg for Vector<Sp, U, N> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::from_components(self.components.map(|c| -c))
    }
}

impl<Sp: Space, U: Unit, const N: usize> Sub for Point<Sp, U, N> {
    type Output = Vector<Sp, U, N>;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Vector::from_components(core::array::from_fn(|i| self.coordinates[i] - rhs.coordinates[i]))
    }
}

impl<Sp: Space, U: Unit, const N: usize> Add<Vector<Sp, U, N>> for Point<Sp, U, N> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Vector<Sp, U, N>) -> Self::Output {
        Self::from_coordinates(core::array::from_fn(|i| self.coordinates[i] + rhs.components[i]))
    }
}

impl<Sp: Space, U: Unit, const N: usize> Sub<Vector<Sp, U, N>> for Point<Sp, U, N> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Vector<Sp, U, N>) -> Self::Output {
        Self::from_coordinates(core::array::from_fn(|i| self.coordinates[i] - rhs.components[i]))
    }
}

#[inline]
fn two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    let bb = s - a;
    let err = (a - (s - bb)) + (b - bb);
    (s, err)
}

#[inline]
fn normalize_pair(hi: f64, lo: f64) -> (f64, f64) {
    let (sum, err) = two_sum(hi, lo);
    let (sum2, err2) = two_sum(sum, err);
    (sum2, err2)
}

/// A compensated quantity stored as `(hi, lo)`.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SplitQuantity<U: Unit> {
    hi: Quantity<U>,
    lo: Quantity<U>,
}

impl<U: Unit> SplitQuantity<U> {
    /// Creates a split quantity from already-normalized storage parts.
    ///
    /// This is intended for constants and low-level storage adapters. Prefer
    /// [`SplitQuantity::new`] when the parts are not already normalized.
    #[inline]
    #[must_use]
    pub const fn from_normalized_parts(hi: Quantity<U>, lo: Quantity<U>) -> Self {
        Self { hi, lo }
    }

    /// Creates a normalized split quantity.
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>, R: Into<Quantity<U>>>(hi: T, lo: R) -> Self {
        let hi = hi.into();
        let lo = lo.into();
        let (hi, lo) = normalize_pair(hi.value(), lo.value());
        Self {
            hi: Quantity::new(hi),
            lo: Quantity::new(lo),
        }
    }

    /// Creates a split quantity from a single quantity.
    #[inline]
    #[must_use]
    pub fn from_quantity<T: Into<Quantity<U>>>(value: T) -> Self {
        Self::new(value, Quantity::<U>::new(0.0))
    }

    /// Returns the high component.
    #[inline]
    #[must_use]
    pub fn hi(self) -> Quantity<U> {
        self.hi
    }

    /// Returns the low component.
    #[inline]
    #[must_use]
    pub fn lo(self) -> Quantity<U> {
        self.lo
    }

    /// Returns the stored split pair.
    #[inline]
    #[must_use]
    pub fn pair(self) -> (Quantity<U>, Quantity<U>) {
        (self.hi, self.lo)
    }

    /// Returns `hi + lo`.
    #[inline]
    #[must_use]
    pub fn total(self) -> Quantity<U> {
        self.hi + self.lo
    }

    /// Converts to another unit of the same dimension.
    #[inline]
    #[must_use]
    pub fn to_unit<U2: Unit<Dim = U::Dim>>(self) -> SplitQuantity<U2> {
        SplitQuantity::new(self.hi.to::<U2>(), self.lo.to::<U2>())
    }

    /// Adds a quantity to the compensated low component and renormalizes.
    #[inline]
    #[must_use]
    pub fn add_quantity(self, rhs: Quantity<U>) -> Self {
        Self::new(self.hi, self.lo + rhs)
    }

    /// Subtracts a quantity from the compensated low component and renormalizes.
    #[inline]
    #[must_use]
    pub fn sub_quantity(self, rhs: Quantity<U>) -> Self {
        Self::new(self.hi, self.lo - rhs)
    }

    /// Scales both components by a dimensionless scalar and renormalizes.
    #[inline]
    #[must_use]
    pub fn scale(self, factor: f64) -> Self {
        Self::new(scaled(self.hi, factor), scaled(self.lo, factor))
    }

    /// Returns `self - rhs` as a single quantity.
    #[inline]
    #[must_use]
    pub fn difference(self, rhs: Self) -> Quantity<U> {
        (self.hi - rhs.hi) + (self.lo - rhs.lo)
    }
}

impl<U: Unit> Add<Quantity<U>> for SplitQuantity<U> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Quantity<U>) -> Self::Output {
        self.add_quantity(rhs)
    }
}

impl<U: Unit> Sub<Quantity<U>> for SplitQuantity<U> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Quantity<U>) -> Self::Output {
        self.sub_quantity(rhs)
    }
}

impl<U: Unit> Sub for SplitQuantity<U> {
    type Output = Quantity<U>;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self.difference(rhs)
    }
}

/// A compensated one-dimensional point.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SplitPoint1<Sp: Space, U: Unit> {
    coordinate: SplitQuantity<U>,
    _space: PhantomData<Sp>,
}

/// A compensated one-dimensional free vector.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SplitVector1<Sp: Space, U: Unit> {
    component: SplitQuantity<U>,
    _space: PhantomData<Sp>,
}

impl<Sp: Space, U: Unit> SplitPoint1<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>, R: Into<Quantity<U>>>(hi: T, lo: R) -> Self {
        Self::from_split(SplitQuantity::new(hi, lo))
    }

    #[inline]
    #[must_use]
    pub const fn from_split(coordinate: SplitQuantity<U>) -> Self {
        Self {
            coordinate,
            _space: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn coordinate(self) -> SplitQuantity<U> {
        self.coordinate
    }

    #[inline]
    #[must_use]
    pub fn total(self) -> Quantity<U> {
        self.coordinate.total()
    }

    #[inline]
    #[must_use]
    pub fn pair(self) -> (Quantity<U>, Quantity<U>) {
        self.coordinate.pair()
    }
}

impl<Sp: Space, U: Unit> SplitVector1<Sp, U> {
    #[inline]
    #[must_use]
    pub fn new<T: Into<Quantity<U>>, R: Into<Quantity<U>>>(hi: T, lo: R) -> Self {
        Self::from_split(SplitQuantity::new(hi, lo))
    }

    #[inline]
    #[must_use]
    pub const fn from_split(component: SplitQuantity<U>) -> Self {
        Self {
            component,
            _space: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn component(self) -> SplitQuantity<U> {
        self.component
    }
}

impl<Sp: Space, U: Unit> Sub for SplitPoint1<Sp, U> {
    type Output = Quantity<U>;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self.coordinate - rhs.coordinate
    }
}

impl<Sp: Space, U: Unit> Add<Quantity<U>> for SplitPoint1<Sp, U> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Quantity<U>) -> Self::Output {
        Self::from_split(self.coordinate + rhs)
    }
}

impl<Sp: Space, U: Unit> Sub<Quantity<U>> for SplitPoint1<Sp, U> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Quantity<U>) -> Self::Output {
        Self::from_split(self.coordinate - rhs)
    }
}

/// One-dimensional affine map between axes with the same unit.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AffineMap1<From: Space, To: Space, U: Unit> {
    source_origin: Quantity<U>,
    target_origin: Quantity<U>,
    scale: f64,
    _spaces: PhantomData<(From, To)>,
}

impl<From: Space, To: Space, U: Unit> AffineMap1<From, To, U> {
    /// Creates `target = target_origin + scale * (source - source_origin)`.
    #[inline]
    #[must_use]
    pub const fn new(source_origin: Quantity<U>, target_origin: Quantity<U>, scale: f64) -> Self {
        Self {
            source_origin,
            target_origin,
            scale,
            _spaces: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn source_origin(self) -> Quantity<U> {
        self.source_origin
    }

    #[inline]
    #[must_use]
    pub fn target_origin(self) -> Quantity<U> {
        self.target_origin
    }

    #[inline]
    #[must_use]
    pub fn scale_factor(self) -> f64 {
        self.scale
    }

    /// Applies this map to an ordinary 1D point.
    #[inline]
    #[must_use]
    pub fn apply_point(self, source: Point1<From, U>) -> Point1<To, U> {
        let delta = source.x() - self.source_origin;
        Point1::new(self.target_origin + scaled(delta, self.scale))
    }

    /// Applies this map to a compensated 1D point.
    #[inline]
    #[must_use]
    pub fn apply_split_point(self, source: SplitPoint1<From, U>) -> SplitPoint1<To, U> {
        let (hi, lo) = source.pair();
        let shifted_hi = hi - self.source_origin;
        let mapped_hi = self.target_origin + scaled(shifted_hi, self.scale);
        let mapped_lo = scaled(lo, self.scale);
        SplitPoint1::from_split(SplitQuantity::new(mapped_hi, mapped_lo))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::{Quantity};
    use qtty::units::{Kilometer, Meter, Second};

    #[derive(Debug, Copy, Clone)]
    struct Axis;
    impl Space for Axis {}

    #[derive(Debug, Copy, Clone)]
    struct OtherAxis;
    impl Space for OtherAxis {}

    #[test]
    fn point_vector_affine_rules() {
        let a = Point2::<Axis, Meter>::new(1.0, 2.0);
        let b = Point2::<Axis, Meter>::new(4.0, 6.0);
        let d = b - a;
        assert_eq!(d.x(), Quantity::<Meter>::new(3.0));
        assert_eq!(d.y(), Quantity::<Meter>::new(4.0));
        let c = a + d;
        assert_eq!(c.x(), Quantity::<Meter>::new(4.0));
        assert_eq!(c.y(), Quantity::<Meter>::new(6.0));
    }

    #[test]
    fn unit_conversion_preserves_space_and_dimension() {
        let p = Point1::<Axis, Kilometer>::new(1.5);
        let meters = p.to_unit::<Meter>();
        assert_eq!(meters.x(), Quantity::<Meter>::new(1500.0));
    }

    #[test]
    fn split_quantity_keeps_compensated_pair_size() {
        assert_eq!(core::mem::size_of::<SplitQuantity<Second>>(), 16);
        assert_eq!(core::mem::size_of::<SplitPoint1<Axis, Second>>(), 16);

        let value = SplitQuantity::<Second>::new(1.0e9, Quantity::<Second>::new(0.25));
        let shifted = value + Quantity::<Second>::new(0.5);
        assert!(
            (shifted.total() - Quantity::<Second>::new(1.0e9 + 0.75)).abs()
                < Quantity::<Second>::new(1e-6)
        );
    }

    #[test]
    fn affine_map1_maps_points_between_axes() {
        let map = AffineMap1::<Axis, OtherAxis, Second>::new(
            Quantity::<Second>::new(10.0),
            Quantity::<Second>::new(100.0),
            2.0,
        );
        let source = Point1::<Axis, Second>::new(12.0);
        let target = map.apply_point(source);
        assert_eq!(target.x(), Quantity::<Second>::new(104.0));

        let split = SplitPoint1::<Axis, Second>::new(12.0, Quantity::<Second>::new(0.25));
        let split_target = map.apply_split_point(split);
        assert!(
            (split_target.total() - Quantity::<Second>::new(104.5)).abs()
                < Quantity::<Second>::new(1e-12)
        );
    }
}
