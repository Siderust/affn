//! 2D unit-typed translation operator.

use qtty::{Quantity, Unit};
use std::marker::PhantomData;

/// A unit-typed translation vector in 2D space.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Translation2<U: Unit> {
    pub v: [f64; 2],
    _unit: PhantomData<U>,
}

impl<U: Unit> Translation2<U> {
    /// Zero translation.
    pub const ZERO: Self = Self {
        v: [0.0, 0.0],
        _unit: PhantomData,
    };

    #[inline]
    #[must_use]
    pub const fn new(x: f64, y: f64) -> Self {
        Self {
            v: [x, y],
            _unit: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub const fn from_array(v: [f64; 2]) -> Self {
        Self {
            v,
            _unit: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn from_quantities(v: [Quantity<U>; 2]) -> Self {
        Self::new(v[0].value(), v[1].value())
    }

    #[inline]
    #[must_use]
    pub fn inverse(&self) -> Self {
        Self::new(-self.v[0], -self.v[1])
    }

    #[inline]
    #[must_use]
    pub fn compose(&self, other: &Self) -> Self {
        Self::new(self.v[0] + other.v[0], self.v[1] + other.v[1])
    }

    #[inline]
    #[must_use]
    pub fn apply_array(&self, v: [f64; 2]) -> [f64; 2] {
        [v[0] + self.v[0], v[1] + self.v[1]]
    }

    #[inline]
    #[must_use]
    pub const fn as_array(&self) -> &[f64; 2] {
        &self.v
    }

    #[inline]
    #[must_use]
    pub fn as_quantities(&self) -> [Quantity<U>; 2] {
        [Quantity::new(self.v[0]), Quantity::new(self.v[1])]
    }

    #[inline]
    #[must_use]
    pub fn to_unit<U2: Unit<Dim = U::Dim>>(&self) -> Translation2<U2> {
        let [x, y] = self.as_quantities();
        Translation2::from_quantities([x.to::<U2>(), y.to::<U2>()])
    }
}

impl<U: Unit> Default for Translation2<U> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<U: Unit> core::ops::Add for Translation2<U> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        self.compose(&rhs)
    }
}

impl<U: Unit> core::ops::Neg for Translation2<U> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.inverse()
    }
}

impl<U: Unit> core::ops::Mul<[f64; 2]> for Translation2<U> {
    type Output = [f64; 2];

    #[inline]
    fn mul(self, rhs: [f64; 2]) -> Self::Output {
        self.apply_array(rhs)
    }
}
