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

impl<U: Unit> core::ops::Mul<[f64; 2]> for Isometry2<U> {
    type Output = [f64; 2];

    #[inline]
    fn mul(self, rhs: [f64; 2]) -> Self::Output {
        self.apply_point(rhs)
    }
}
