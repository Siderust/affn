//! Operator composition used by [`super::Transform::then`].
//!
//! `next.after(previous)` builds the operator that applies `previous` first,
//! then `next`, matching `result = next * previous`.

use crate::ops::{Isometry3, Rotation3, Translation3};
use qtty::Unit;

/// Compose `Self` after `Prev`: apply `Prev` first, then `Self`.
pub trait ComposeAfter<Prev> {
    /// Operator type of the composed transform.
    type Output;
    /// Builds `Self ∘ Prev` (apply `Prev`, then `Self`).
    fn after(self, prev: Prev) -> Self::Output;
}

// -----------------------------------------------------------------------------
// Same-kind composition
// -----------------------------------------------------------------------------

impl ComposeAfter<Rotation3> for Rotation3 {
    type Output = Rotation3;

    #[inline]
    fn after(self, prev: Rotation3) -> Rotation3 {
        // self * prev — apply prev first
        self.compose(&prev)
    }
}

impl<U: Unit> ComposeAfter<Translation3<U>> for Translation3<U> {
    type Output = Translation3<U>;

    #[inline]
    fn after(self, prev: Translation3<U>) -> Translation3<U> {
        // Translations commute; compose as vector sum (self + prev).
        self.compose(&prev)
    }
}

impl<U: Unit> ComposeAfter<Isometry3<U>> for Isometry3<U> {
    type Output = Isometry3<U>;

    #[inline]
    fn after(self, prev: Isometry3<U>) -> Isometry3<U> {
        self.compose(&prev)
    }
}

// -----------------------------------------------------------------------------
// Rotation ↔ Translation → Isometry
// -----------------------------------------------------------------------------

impl<U: Unit> ComposeAfter<Rotation3> for Translation3<U> {
    type Output = Isometry3<U>;

    #[inline]
    fn after(self, prev: Rotation3) -> Isometry3<U> {
        // Translation * Rotation = (R, t)
        Isometry3::new(prev, self)
    }
}

impl<U: Unit> ComposeAfter<Translation3<U>> for Rotation3 {
    type Output = Isometry3<U>;

    #[inline]
    fn after(self, prev: Translation3<U>) -> Isometry3<U> {
        // Rotation * Translation = (R, R * t)
        let rotated_t = self.apply_array(prev.v);
        Isometry3::new(self, Translation3::from_array(rotated_t))
    }
}

// -----------------------------------------------------------------------------
// Mixing with Isometry3
// -----------------------------------------------------------------------------

impl<U: Unit> ComposeAfter<Rotation3> for Isometry3<U> {
    type Output = Isometry3<U>;

    #[inline]
    fn after(self, prev: Rotation3) -> Isometry3<U> {
        self.compose(&Isometry3::from_rotation(prev))
    }
}

impl<U: Unit> ComposeAfter<Isometry3<U>> for Rotation3 {
    type Output = Isometry3<U>;

    #[inline]
    fn after(self, prev: Isometry3<U>) -> Isometry3<U> {
        Isometry3::from_rotation(self).compose(&prev)
    }
}

impl<U: Unit> ComposeAfter<Translation3<U>> for Isometry3<U> {
    type Output = Isometry3<U>;

    #[inline]
    fn after(self, prev: Translation3<U>) -> Isometry3<U> {
        self.compose(&Isometry3::from_translation(prev))
    }
}

impl<U: Unit> ComposeAfter<Isometry3<U>> for Translation3<U> {
    type Output = Isometry3<U>;

    #[inline]
    fn after(self, prev: Isometry3<U>) -> Isometry3<U> {
        Isometry3::from_translation(self).compose(&prev)
    }
}
