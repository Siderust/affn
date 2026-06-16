//! Interpolation abscissa types.

use qtty::{Quantity, Unit};

/// An ordered interpolation abscissa.
///
/// Implemented for raw scalar parameters and typed `qtty` quantities. New
/// interpolation APIs should use this trait instead of exposing separate raw
/// and quantity table types.
pub trait InterpolationAbscissa: Copy {
    /// Difference between two abscissae.
    type Delta: Copy;

    /// Returns the raw scalar used for ordering and normalized interpolation.
    fn raw(self) -> f64;

    /// Builds a delta value from a raw difference in this abscissa' stored unit.
    fn delta_from_raw(raw: f64) -> Self::Delta;
}

impl InterpolationAbscissa for f64 {
    type Delta = f64;

    #[inline]
    fn raw(self) -> f64 {
        self
    }

    #[inline]
    fn delta_from_raw(raw: f64) -> Self::Delta {
        raw
    }
}

impl<U: Unit> InterpolationAbscissa for Quantity<U> {
    type Delta = Quantity<U>;

    #[inline]
    fn raw(self) -> f64 {
        self.value()
    }

    #[inline]
    fn delta_from_raw(raw: f64) -> Self::Delta {
        Quantity::<U>::new(raw)
    }
}
