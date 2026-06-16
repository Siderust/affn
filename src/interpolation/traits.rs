//! Traits for interpolating complete typed values.

use super::abscissa::InterpolationAbscissa;
use crate::cartesian::{Position, Vector};
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::length::LengthUnit;
use qtty::{Quantity, Unit, UnitDiv, UnitMul};

/// Basis coefficients for one cubic Hermite segment.
#[derive(Debug, Clone, Copy)]
pub struct HermiteBasis<X: InterpolationAbscissa> {
    /// Value basis for the first endpoint.
    pub h00: f64,
    /// Derivative basis for the first endpoint, scaled by the abscissa delta.
    pub h10_dx: X::Delta,
    /// Value basis for the second endpoint.
    pub h01: f64,
    /// Derivative basis for the second endpoint, scaled by the abscissa delta.
    pub h11_dx: X::Delta,
    /// First derivative of `h00` with respect to normalized segment parameter.
    pub dh00_over_dt: f64,
    /// First derivative of `h10` with respect to normalized segment parameter.
    pub dh10_over_dt: f64,
    /// First derivative of `h01` with respect to normalized segment parameter.
    pub dh01_over_dt: f64,
    /// First derivative of `h11` with respect to normalized segment parameter.
    pub dh11_over_dt: f64,
    /// Full abscissa delta for the segment.
    pub dx: X::Delta,
    /// Raw inverse abscissa delta, for scalar-abscissa implementations.
    pub inv_raw_dx: f64,
}

impl<X: InterpolationAbscissa> HermiteBasis<X> {
    /// Constructs a basis from normalized `t` and raw segment width.
    #[inline]
    pub(crate) fn new(t: f64, raw_dx: f64) -> Self {
        let t2 = t * t;
        let t3 = t2 * t;

        Self {
            h00: 2.0 * t3 - 3.0 * t2 + 1.0,
            h10_dx: X::delta_from_raw((t3 - 2.0 * t2 + t) * raw_dx),
            h01: -2.0 * t3 + 3.0 * t2,
            h11_dx: X::delta_from_raw((t3 - t2) * raw_dx),
            dh00_over_dt: 6.0 * t2 - 6.0 * t,
            dh10_over_dt: 3.0 * t2 - 4.0 * t + 1.0,
            dh01_over_dt: -6.0 * t2 + 6.0 * t,
            dh11_over_dt: 3.0 * t2 - 2.0 * t,
            dx: X::delta_from_raw(raw_dx),
            inv_raw_dx: 1.0 / raw_dx,
        }
    }
}

/// A value that can be combined by cubic Hermite interpolation over abscissa
/// type `X`.
///
/// Implementations operate on complete typed values, preserving all frame,
/// center, and unit tags carried by the type.
pub trait HermiteInterpolable<X: InterpolationAbscissa>: Sized {
    /// Derivative type with respect to the interpolation abscissa.
    type Derivative;

    /// Combines endpoint values and derivatives into an interpolated value.
    fn hermite_value(
        basis: HermiteBasis<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self;

    /// Combines endpoint values and derivatives into an interpolated derivative.
    fn hermite_derivative(
        basis: HermiteBasis<X>,
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

impl HermiteInterpolable<f64> for f64 {
    type Derivative = f64;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        basis.h00 * y0 + basis.h10_dx * dy0 + basis.h01 * y1 + basis.h11_dx * dy1
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        basis.dh00_over_dt * basis.inv_raw_dx * y0
            + basis.dh10_over_dt * dy0
            + basis.dh01_over_dt * basis.inv_raw_dx * y1
            + basis.dh11_over_dt * dy1
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

impl<X: Unit> HermiteInterpolable<Quantity<X>> for f64 {
    type Derivative = f64;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        basis.h00 * y0 + basis.h10_dx.value() * dy0 + basis.h01 * y1 + basis.h11_dx.value() * dy1
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        basis.dh00_over_dt * basis.inv_raw_dx * y0
            + basis.dh10_over_dt * dy0
            + basis.dh01_over_dt * basis.inv_raw_dx * y1
            + basis.dh11_over_dt * dy1
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

impl<U: Unit> HermiteInterpolable<f64> for Quantity<U> {
    type Derivative = Quantity<U>;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        y0 * basis.h00 + dy0 * basis.h10_dx + y1 * basis.h01 + dy1 * basis.h11_dx
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0 * (basis.dh00_over_dt * basis.inv_raw_dx)
            + dy0 * basis.dh10_over_dt
            + y1 * (basis.dh01_over_dt * basis.inv_raw_dx)
            + dy1 * basis.dh11_over_dt
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

impl<X, U> HermiteInterpolable<Quantity<X>> for Quantity<U>
where
    X: Unit,
    U: Unit + UnitDiv<X>,
    <U as UnitDiv<X>>::Output: Unit + UnitMul<X, Output = U>,
{
    type Derivative = Quantity<<U as UnitDiv<X>>::Output>;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        y0 * basis.h00 + (dy0 * basis.h10_dx) + y1 * basis.h01 + (dy1 * basis.h11_dx)
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        (y0 / basis.dx) * basis.dh00_over_dt
            + dy0 * basis.dh10_over_dt
            + (y1 / basis.dx) * basis.dh01_over_dt
            + dy1 * basis.dh11_over_dt
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

impl<F, U> HermiteInterpolable<f64> for Vector<F, U>
where
    F: ReferenceFrame,
    U: Unit,
{
    type Derivative = Vector<F, U>;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        y0.scale(basis.h00)
            + dy0.scale(basis.h10_dx)
            + y1.scale(basis.h01)
            + dy1.scale(basis.h11_dx)
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0.scale(basis.dh00_over_dt * basis.inv_raw_dx)
            + dy0.scale(basis.dh10_over_dt)
            + y1.scale(basis.dh01_over_dt * basis.inv_raw_dx)
            + dy1.scale(basis.dh11_over_dt)
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

impl<X, F, U> HermiteInterpolable<Quantity<X>> for Vector<F, U>
where
    X: Unit,
    F: ReferenceFrame,
    U: Unit + UnitDiv<X>,
    <U as UnitDiv<X>>::Output: Unit + UnitMul<X, Output = U>,
{
    type Derivative = Vector<F, <U as UnitDiv<X>>::Output>;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        y0.scale(basis.h00) + (dy0 * basis.h10_dx) + y1.scale(basis.h01) + (dy1 * basis.h11_dx)
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0.div_quantity(basis.dx).scale(basis.dh00_over_dt)
            + dy0.scale(basis.dh10_over_dt)
            + y1.div_quantity(basis.dx).scale(basis.dh01_over_dt)
            + dy1.scale(basis.dh11_over_dt)
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

impl<C, F, U> HermiteInterpolable<f64> for Position<C, F, U>
where
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Derivative = Vector<F, U>;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        let chord = y1 - y0;
        y0 + chord.scale(basis.h01) + dy0.scale(basis.h10_dx) + dy1.scale(basis.h11_dx)
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        let chord = y1 - y0;
        chord.scale(basis.dh01_over_dt * basis.inv_raw_dx)
            + dy0.scale(basis.dh10_over_dt)
            + dy1.scale(basis.dh11_over_dt)
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

impl<X, C, F, L> HermiteInterpolable<Quantity<X>> for Position<C, F, L>
where
    X: Unit,
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
    L: LengthUnit + UnitDiv<X>,
    <L as UnitDiv<X>>::Output: Unit + UnitMul<X, Output = L>,
{
    type Derivative = Vector<F, <L as UnitDiv<X>>::Output>;

    #[inline]
    fn hermite_value(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        let chord = y1 - y0;
        y0 + chord.scale(basis.h01) + (dy0 * basis.h10_dx) + (dy1 * basis.h11_dx)
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        let chord = y1 - y0;
        chord.div_quantity(basis.dx).scale(basis.dh01_over_dt)
            + dy0.scale(basis.dh10_over_dt)
            + dy1.scale(basis.dh11_over_dt)
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
