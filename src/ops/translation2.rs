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

forward_ref_binop! { impl[U: Unit] Add, add for Translation2<U>, Translation2<U> }

impl<U: Unit> core::ops::Neg for Translation2<U> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.inverse()
    }
}

forward_ref_unop! { impl[U: Unit] Neg, neg for Translation2<U> }

impl<U: Unit> core::ops::Mul<[f64; 2]> for Translation2<U> {
    type Output = [f64; 2];

    #[inline]
    fn mul(self, rhs: [f64; 2]) -> Self::Output {
        self.apply_array(rhs)
    }
}

forward_ref_binop! { impl[U: Unit] Mul, mul for Translation2<U>, [f64; 2] }

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::units::Meter;
    use qtty::M;

    #[test]
    fn zero_is_default() {
        let t: Translation2<Meter> = Default::default();
        assert_eq!(t, Translation2::ZERO);
    }

    #[test]
    fn new_stores_components() {
        let t = Translation2::<Meter>::new(3.0, 4.0);
        assert_eq!(t.v, [3.0, 4.0]);
    }

    #[test]
    fn from_array_round_trip() {
        let arr = [1.5, -2.5];
        let t = Translation2::<Meter>::from_array(arr);
        assert_eq!(t.as_array(), &arr);
    }

    #[test]
    fn from_quantities_round_trip() {
        let qs = [1.0 * M, 2.0 * M];
        let t = Translation2::from_quantities(qs);
        let back = t.as_quantities();
        assert_eq!(back[0], 1.0 * M);
        assert_eq!(back[1], 2.0 * M);
    }

    #[test]
    fn inverse_negates() {
        let t = Translation2::<Meter>::new(3.0, -4.0);
        let inv = t.inverse();
        assert_eq!(inv.v, [-3.0, 4.0]);
    }

    #[test]
    fn neg_operator_same_as_inverse() {
        let t = Translation2::<Meter>::new(1.0, 2.0);
        assert_eq!(-t, t.inverse());
    }

    #[test]
    fn compose_adds() {
        let a = Translation2::<Meter>::new(1.0, 2.0);
        let b = Translation2::<Meter>::new(3.0, 4.0);
        let c = a.compose(&b);
        assert_eq!(c.v, [4.0, 6.0]);
    }

    #[test]
    fn add_operator_same_as_compose() {
        let a = Translation2::<Meter>::new(1.0, 2.0);
        let b = Translation2::<Meter>::new(3.0, 4.0);
        assert_eq!(a + b, a.compose(&b));
    }

    #[test]
    fn apply_array_shifts_point() {
        let t = Translation2::<Meter>::new(10.0, 20.0);
        assert_eq!(t.apply_array([1.0, 2.0]), [11.0, 22.0]);
    }

    #[test]
    fn mul_array_same_as_apply_array() {
        let t = Translation2::<Meter>::new(5.0, -5.0);
        let v = [1.0, 2.0];
        assert_eq!(t * v, t.apply_array(v));
    }

    #[test]
    fn to_unit_converts() {
        use qtty::units::Kilometer;
        let t = Translation2::<Meter>::new(1000.0, 2000.0);
        let t_km: Translation2<Kilometer> = t.to_unit();
        assert!((t_km.v[0] - 1.0).abs() < 1e-10);
        assert!((t_km.v[1] - 2.0).abs() < 1e-10);
    }
}
