//! 2D rigid body transform.

use super::{Rotation2, Translation2};
use qtty::Unit;
use std::marker::PhantomData;

/// A 2D isometry combining rotation and unit-typed translation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Isometry2<U: Unit> {
    pub rotation: Rotation2,
    pub translation: Translation2<U>,
    _unit: PhantomData<U>,
}

impl<U: Unit> Isometry2<U> {
    /// Identity isometry.
    pub const IDENTITY: Self = Self {
        rotation: Rotation2::IDENTITY,
        translation: Translation2::ZERO,
        _unit: PhantomData,
    };

    #[inline]
    #[must_use]
    pub const fn new(rotation: Rotation2, translation: Translation2<U>) -> Self {
        Self {
            rotation,
            translation,
            _unit: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub const fn from_rotation(rotation: Rotation2) -> Self {
        Self {
            rotation,
            translation: Translation2::ZERO,
            _unit: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub const fn from_translation(translation: Translation2<U>) -> Self {
        Self {
            rotation: Rotation2::IDENTITY,
            translation,
            _unit: PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn inverse(&self) -> Self {
        let r_inv = self.rotation.inverse();
        let t_inv = r_inv.apply_array(self.translation.v);
        Self::new(r_inv, Translation2::new(-t_inv[0], -t_inv[1]))
    }

    #[inline]
    #[must_use]
    pub fn compose(&self, other: &Self) -> Self {
        let rotation = self.rotation.compose(&other.rotation);
        let rotated_t = self.rotation.apply_array(other.translation.v);
        let translation = Translation2::new(
            rotated_t[0] + self.translation.v[0],
            rotated_t[1] + self.translation.v[1],
        );
        Self::new(rotation, translation)
    }

    #[inline]
    #[must_use]
    pub fn apply_point(&self, p: [f64; 2]) -> [f64; 2] {
        self.translation.apply_array(self.rotation.apply_array(p))
    }

    #[inline]
    #[must_use]
    pub fn apply_vector(&self, v: [f64; 2]) -> [f64; 2] {
        self.rotation.apply_array(v)
    }
}

impl<U: Unit> Default for Isometry2<U> {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl<U: Unit> core::ops::Mul for Isometry2<U> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        self.compose(&rhs)
    }
}

forward_ref_binop! { impl[U: Unit] Mul, mul for Isometry2<U>, Isometry2<U> }

impl<U: Unit> core::ops::Mul<[f64; 2]> for Isometry2<U> {
    type Output = [f64; 2];

    #[inline]
    fn mul(self, rhs: [f64; 2]) -> Self::Output {
        self.apply_point(rhs)
    }
}

forward_ref_binop! { impl[U: Unit] Mul, mul for Isometry2<U>, [f64; 2] }

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::angular::Radians;
    use qtty::units::Meter;
    use std::f64::consts::FRAC_PI_2;

    fn approx_eq(a: f64, b: f64) -> bool {
        (a - b).abs() < 1e-12
    }

    fn approx_eq_arr(a: [f64; 2], b: [f64; 2]) -> bool {
        approx_eq(a[0], b[0]) && approx_eq(a[1], b[1])
    }

    #[test]
    fn identity_is_default() {
        let id: Isometry2<Meter> = Default::default();
        assert_eq!(id, Isometry2::IDENTITY);
    }

    #[test]
    fn from_rotation_has_zero_translation() {
        let r = Rotation2::new(Radians::new(FRAC_PI_2));
        let iso = Isometry2::<Meter>::from_rotation(r);
        assert_eq!(iso.translation, Translation2::ZERO);
        assert_eq!(iso.rotation, r);
    }

    #[test]
    fn from_translation_has_identity_rotation() {
        let t = Translation2::<Meter>::new(3.0, 4.0);
        let iso = Isometry2::from_translation(t);
        assert_eq!(iso.rotation, Rotation2::IDENTITY);
        assert_eq!(iso.translation, t);
    }

    #[test]
    fn apply_point_translates_and_rotates() {
        let r = Rotation2::new(Radians::new(FRAC_PI_2));
        let t = Translation2::<Meter>::new(1.0, 2.0);
        let iso = Isometry2::new(r, t);
        // rotate [1,0] by 90° → [0,1], then translate by [1,2] → [1,3]
        let result = iso.apply_point([1.0, 0.0]);
        assert!(approx_eq(result[0], 1.0));
        assert!(approx_eq(result[1], 3.0));
    }

    #[test]
    fn apply_vector_rotation_only() {
        let r = Rotation2::new(Radians::new(FRAC_PI_2));
        let iso = Isometry2::<Meter>::new(r, Translation2::new(100.0, 200.0));
        // vectors are not affected by translation
        let result = iso.apply_vector([1.0, 0.0]);
        assert!(approx_eq(result[0], 0.0));
        assert!(approx_eq(result[1], 1.0));
    }

    #[test]
    fn inverse_roundtrip() {
        let r = Rotation2::new(Radians::new(0.7));
        let t = Translation2::<Meter>::new(3.0, -5.0);
        let iso = Isometry2::new(r, t);
        let p = [2.0, 3.0];
        let inv = iso.inverse();
        let roundtrip = inv.apply_point(iso.apply_point(p));
        assert!(approx_eq_arr(roundtrip, p));
    }

    #[test]
    fn compose_same_as_mul() {
        let r1 = Rotation2::new(Radians::new(0.5));
        let t1 = Translation2::<Meter>::new(1.0, 0.0);
        let r2 = Rotation2::new(Radians::new(0.3));
        let t2 = Translation2::<Meter>::new(0.0, 2.0);
        let a = Isometry2::new(r1, t1);
        let b = Isometry2::new(r2, t2);
        assert_eq!(a * b, a.compose(&b));
    }

    #[test]
    fn mul_array_same_as_apply_point() {
        let r = Rotation2::new(Radians::new(1.0));
        let t = Translation2::<Meter>::new(2.0, 3.0);
        let iso = Isometry2::new(r, t);
        let p = [4.0, 5.0];
        assert_eq!(iso * p, iso.apply_point(p));
    }
}
