//! Interpolation abscissa types.

use super::InterpolationError;
use qtty::{Quantity, Unit};
use std::cmp::Ordering;

mod sealed {
    pub trait Sealed {}
    impl Sealed for f64 {}
    impl<U: qtty::Unit> Sealed for qtty::Quantity<U> {}
}

/// Difference between two interpolation abscissae.
pub trait AbscissaDelta: Copy {
    /// Scales this delta by a dimensionless Hermite basis coefficient.
    fn scale(self, factor: f64) -> Self;

    /// Raw value used only for diagnostics and scalar-only formulas.
    fn diagnostic_raw(self) -> f64;
}

impl AbscissaDelta for f64 {
    #[inline]
    fn scale(self, factor: f64) -> Self {
        self * factor
    }

    #[inline]
    fn diagnostic_raw(self) -> f64 {
        self
    }
}

impl<U: Unit> AbscissaDelta for Quantity<U> {
    #[inline]
    fn scale(self, factor: f64) -> Self {
        self * factor
    }

    #[inline]
    fn diagnostic_raw(self) -> f64 {
        self.value()
    }
}

/// An ordered interpolation abscissa.
///
/// Physical domains should use typed [`qtty::Quantity`] abscissae. The raw
/// `f64` implementation is intended for explicitly scalar, dimensionless
/// interpolation such as `CubicHermiteTable<f64, f64>`.
pub trait InterpolationAbscissa: sealed::Sealed + Copy {
    /// Difference between two abscissae.
    type Delta: AbscissaDelta;

    /// Returns whether this abscissa is finite.
    fn is_finite(self) -> bool;

    /// Compares two abscissae for table ordering.
    fn cmp_abscissa(self, other: Self) -> Ordering;

    /// Returns `self - origin` as a typed delta.
    fn delta_since(self, origin: Self) -> Self::Delta;

    /// Returns the normalized segment coordinate in `[0, 1]`.
    fn normalize_between(self, start: Self, end: Self) -> Result<f64, InterpolationError>;

    /// Raw value used only for diagnostics.
    fn diagnostic_raw(self) -> f64;
}

impl InterpolationAbscissa for f64 {
    type Delta = f64;

    #[inline]
    fn is_finite(self) -> bool {
        self.is_finite()
    }

    #[inline]
    fn cmp_abscissa(self, other: Self) -> Ordering {
        self.total_cmp(&other)
    }

    #[inline]
    fn delta_since(self, origin: Self) -> Self::Delta {
        self - origin
    }

    #[inline]
    fn normalize_between(self, start: Self, end: Self) -> Result<f64, InterpolationError> {
        Ok((self - start) / (end - start))
    }

    #[inline]
    fn diagnostic_raw(self) -> f64 {
        self
    }
}

impl<U: Unit> InterpolationAbscissa for Quantity<U> {
    type Delta = Quantity<U>;

    #[inline]
    fn is_finite(self) -> bool {
        self.value().is_finite()
    }

    #[inline]
    fn cmp_abscissa(self, other: Self) -> Ordering {
        self.value().total_cmp(&other.value())
    }

    #[inline]
    fn delta_since(self, origin: Self) -> Self::Delta {
        self - origin
    }

    #[inline]
    fn normalize_between(self, start: Self, end: Self) -> Result<f64, InterpolationError> {
        let offset = self - start;
        let width = end - start;
        Ok(offset.value() / width.value())
    }

    #[inline]
    fn diagnostic_raw(self) -> f64 {
        self.value()
    }
}
