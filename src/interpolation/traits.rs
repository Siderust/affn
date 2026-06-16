//! Traits for interpolating complete typed values.

use super::abscissa::{AbscissaDelta, InterpolationAbscissa};
use crate::cartesian::{Position, Vector};
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::length::LengthUnit;
use qtty::{Quantity, Unit, UnitDiv, UnitMul};

/// Basis coefficients for one cubic Hermite segment.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct HermiteBasis<A: InterpolationAbscissa> {
    h00: f64,
    h10_dx: A::Delta,
    h01: f64,
    h11_dx: A::Delta,
    dh00_dt: f64,
    dh10_dt: f64,
    dh01_dt: f64,
    dh11_dt: f64,
    dx: A::Delta,
}

impl<A: InterpolationAbscissa> HermiteBasis<A> {
    /// Constructs a basis from normalized `tau` and typed segment width.
    #[inline]
    pub(crate) fn new(tau: f64, dx: A::Delta) -> Self {
        let tau2 = tau * tau;
        let tau3 = tau2 * tau;

        Self {
            h00: 2.0 * tau3 - 3.0 * tau2 + 1.0,
            h10_dx: dx.scale(tau3 - 2.0 * tau2 + tau),
            h01: -2.0 * tau3 + 3.0 * tau2,
            h11_dx: dx.scale(tau3 - tau2),
            dh00_dt: 6.0 * tau2 - 6.0 * tau,
            dh10_dt: 3.0 * tau2 - 4.0 * tau + 1.0,
            dh01_dt: -6.0 * tau2 + 6.0 * tau,
            dh11_dt: 3.0 * tau2 - 2.0 * tau,
            dx,
        }
    }

    /// Value basis for the first endpoint.
    #[inline]
    pub fn h00(&self) -> f64 {
        self.h00
    }

    /// Derivative basis for the first endpoint, scaled by segment width.
    #[inline]
    pub fn h10_dx(&self) -> A::Delta {
        self.h10_dx
    }

    /// Value basis for the second endpoint.
    #[inline]
    pub fn h01(&self) -> f64 {
        self.h01
    }

    /// Derivative basis for the second endpoint, scaled by segment width.
    #[inline]
    pub fn h11_dx(&self) -> A::Delta {
        self.h11_dx
    }

    /// Normalized derivative of `h00`.
    #[inline]
    pub fn dh00_dt(&self) -> f64 {
        self.dh00_dt
    }

    /// Normalized derivative of `h10`.
    #[inline]
    pub fn dh10_dt(&self) -> f64 {
        self.dh10_dt
    }

    /// Normalized derivative of `h01`.
    #[inline]
    pub fn dh01_dt(&self) -> f64 {
        self.dh01_dt
    }

    /// Normalized derivative of `h11`.
    #[inline]
    pub fn dh11_dt(&self) -> f64 {
        self.dh11_dt
    }

    /// Typed segment width.
    #[inline]
    pub fn dx(&self) -> A::Delta {
        self.dx
    }
}

/// A value that can be combined by cubic Hermite interpolation over abscissa
/// type `X`.
///
/// Implementations operate on complete typed values, preserving all frame,
/// center, and unit tags carried by the type.
pub trait HermiteInterpolable<A: InterpolationAbscissa>: Sized {
    /// Derivative type with respect to the interpolation abscissa.
    type Derivative;

    /// Combines endpoint values and derivatives into an interpolated value.
    fn hermite_value(
        basis: HermiteBasis<A>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self;

    /// Combines endpoint values and derivatives into an interpolated derivative.
    fn hermite_derivative(
        basis: HermiteBasis<A>,
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
        basis.h00() * y0 + basis.h10_dx() * dy0 + basis.h01() * y1 + basis.h11_dx() * dy1
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        (basis.dh00_dt() * y0 + basis.dh01_dt() * y1) / AbscissaDelta::diagnostic_raw(basis.dx())
            + basis.dh10_dt() * dy0
            + basis.dh11_dt() * dy1
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
        y0 * basis.h00() + dy0 * basis.h10_dx() + y1 * basis.h01() + dy1 * basis.h11_dx()
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0 * (basis.dh00_dt() / AbscissaDelta::diagnostic_raw(basis.dx()))
            + dy0 * basis.dh10_dt()
            + y1 * (basis.dh01_dt() / AbscissaDelta::diagnostic_raw(basis.dx()))
            + dy1 * basis.dh11_dt()
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
        y0 * basis.h00() + (dy0 * basis.h10_dx()) + y1 * basis.h01() + (dy1 * basis.h11_dx())
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        (y0 / basis.dx()) * basis.dh00_dt()
            + dy0 * basis.dh10_dt()
            + (y1 / basis.dx()) * basis.dh01_dt()
            + dy1 * basis.dh11_dt()
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
        y0.scale(basis.h00())
            + dy0.scale(basis.h10_dx())
            + y1.scale(basis.h01())
            + dy1.scale(basis.h11_dx())
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<f64>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0.scale(basis.dh00_dt() / AbscissaDelta::diagnostic_raw(basis.dx()))
            + dy0.scale(basis.dh10_dt())
            + y1.scale(basis.dh01_dt() / AbscissaDelta::diagnostic_raw(basis.dx()))
            + dy1.scale(basis.dh11_dt())
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
        y0.scale(basis.h00())
            + (dy0 * basis.h10_dx())
            + y1.scale(basis.h01())
            + (dy1 * basis.h11_dx())
    }

    #[inline]
    fn hermite_derivative(
        basis: HermiteBasis<Quantity<X>>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        y0.div_quantity(basis.dx()).scale(basis.dh00_dt())
            + dy0.scale(basis.dh10_dt())
            + y1.div_quantity(basis.dx()).scale(basis.dh01_dt())
            + dy1.scale(basis.dh11_dt())
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
        y0 + chord.scale(basis.h01()) + dy0.scale(basis.h10_dx()) + dy1.scale(basis.h11_dx())
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
        chord.scale(basis.dh01_dt() / AbscissaDelta::diagnostic_raw(basis.dx()))
            + dy0.scale(basis.dh10_dt())
            + dy1.scale(basis.dh11_dt())
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
        y0 + chord.scale(basis.h01()) + (dy0 * basis.h10_dx()) + (dy1 * basis.h11_dx())
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
        chord.div_quantity(basis.dx()).scale(basis.dh01_dt())
            + dy0.scale(basis.dh10_dt())
            + dy1.scale(basis.dh11_dt())
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
