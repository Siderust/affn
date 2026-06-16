//! Traits for interpolating complete typed values.

use crate::cartesian::{Position, Vector};
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::length::LengthUnit;
use qtty::{Quantity, Unit};

/// A value that can be combined by cubic Hermite interpolation.
///
/// Implementations operate on complete typed values, preserving all frame,
/// center, and unit tags carried by the type.
pub trait HermiteInterpolable: Sized {
    /// Derivative type with respect to the scalar interpolation abscissa.
    type Derivative;

    /// Combines endpoint values and derivatives into an interpolated value.
    fn hermite_combine(
        h00: f64,
        h10_dt: f64,
        h01: f64,
        h11_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self;

    /// Combines endpoint values and derivatives into an interpolated derivative.
    fn hermite_derivative_combine(
        dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        inv_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative;

    /// Returns whether this value is finite.
    fn hermite_value_is_finite(&self) -> bool {
        true
    }

    /// Returns whether this derivative is finite.
    fn hermite_derivative_is_finite(_derivative: &Self::Derivative) -> bool {
        true
    }
}

impl HermiteInterpolable for f64 {
    type Derivative = f64;

    #[inline]
    fn hermite_combine(
        h00: f64,
        h10_dt: f64,
        h01: f64,
        h11_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        h00 * y0 + h10_dt * dy0 + h01 * y1 + h11_dt * dy1
    }

    #[inline]
    fn hermite_derivative_combine(
        dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        inv_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        dh00_over_dt * inv_dt * y0
            + dh10_over_dt * dy0
            + dh01_over_dt * inv_dt * y1
            + dh11_over_dt * dy1
    }

    #[inline]
    fn hermite_value_is_finite(&self) -> bool {
        self.is_finite()
    }

    #[inline]
    fn hermite_derivative_is_finite(derivative: &Self::Derivative) -> bool {
        derivative.is_finite()
    }
}

impl<U: Unit> HermiteInterpolable for Quantity<U> {
    type Derivative = Quantity<U>;

    #[inline]
    fn hermite_combine(
        h00: f64,
        h10_dt: f64,
        h01: f64,
        h11_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        y0 * h00 + dy0 * h10_dt + y1 * h01 + dy1 * h11_dt
    }

    #[inline]
    fn hermite_derivative_combine(
        dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        inv_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0 * (dh00_over_dt * inv_dt)
            + dy0 * dh10_over_dt
            + y1 * (dh01_over_dt * inv_dt)
            + dy1 * dh11_over_dt
    }

    #[inline]
    fn hermite_value_is_finite(&self) -> bool {
        self.value().is_finite()
    }

    #[inline]
    fn hermite_derivative_is_finite(derivative: &Self::Derivative) -> bool {
        derivative.value().is_finite()
    }
}

impl<F, U> HermiteInterpolable for Vector<F, U>
where
    F: ReferenceFrame,
    U: Unit,
{
    type Derivative = Vector<F, U>;

    #[inline]
    fn hermite_combine(
        h00: f64,
        h10_dt: f64,
        h01: f64,
        h11_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        y0.scale(h00) + dy0.scale(h10_dt) + y1.scale(h01) + dy1.scale(h11_dt)
    }

    #[inline]
    fn hermite_derivative_combine(
        dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        inv_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0.scale(dh00_over_dt * inv_dt)
            + dy0.scale(dh10_over_dt)
            + y1.scale(dh01_over_dt * inv_dt)
            + dy1.scale(dh11_over_dt)
    }

    #[inline]
    fn hermite_value_is_finite(&self) -> bool {
        self.x().value().is_finite() && self.y().value().is_finite() && self.z().value().is_finite()
    }

    #[inline]
    fn hermite_derivative_is_finite(derivative: &Self::Derivative) -> bool {
        derivative.x().value().is_finite()
            && derivative.y().value().is_finite()
            && derivative.z().value().is_finite()
    }
}

impl<C, F, U> HermiteInterpolable for Position<C, F, U>
where
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Derivative = Vector<F, U>;

    #[inline]
    fn hermite_combine(
        _h00: f64,
        h10_dt: f64,
        h01: f64,
        h11_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        let chord = y1 - y0;
        y0 + chord.scale(h01) + dy0.scale(h10_dt) + dy1.scale(h11_dt)
    }

    #[inline]
    fn hermite_derivative_combine(
        _dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        inv_dt: f64,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        let chord = y1 - y0;
        chord.scale(dh01_over_dt * inv_dt) + dy0.scale(dh10_over_dt) + dy1.scale(dh11_over_dt)
    }

    #[inline]
    fn hermite_value_is_finite(&self) -> bool {
        self.x().value().is_finite() && self.y().value().is_finite() && self.z().value().is_finite()
    }

    #[inline]
    fn hermite_derivative_is_finite(derivative: &Self::Derivative) -> bool {
        derivative.x().value().is_finite()
            && derivative.y().value().is_finite()
            && derivative.z().value().is_finite()
    }
}
