//! Quantity-abscissa cubic Hermite interpolation tables.

use super::error::InterpolationError;
use super::scalar::hermite_basis;
use crate::cartesian::{Position, Vector};
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::length::LengthUnit;
use qtty::{Quantity, Unit, UnitDiv, UnitMul};

/// A value that can be combined by cubic Hermite interpolation over a typed
/// quantity abscissa.
pub trait QuantityHermiteInterpolable<X: Unit>: Sized {
    /// Derivative type with respect to the abscissa unit `X`.
    type Derivative;

    /// Combines endpoint values and derivatives into an interpolated value.
    fn quantity_hermite_combine(
        h00: f64,
        h10_dx: Quantity<X>,
        h01: f64,
        h11_dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self;

    /// Combines endpoint values and derivatives into an interpolated derivative.
    fn quantity_hermite_derivative_combine(
        dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative;

    /// Returns whether this value is finite.
    fn quantity_hermite_value_is_finite(&self) -> bool {
        true
    }

    /// Returns whether this derivative is finite.
    fn quantity_hermite_derivative_is_finite(_derivative: &Self::Derivative) -> bool {
        true
    }
}

impl<X: Unit> QuantityHermiteInterpolable<X> for f64 {
    type Derivative = f64;

    #[inline]
    fn quantity_hermite_combine(
        h00: f64,
        h10_dx: Quantity<X>,
        h01: f64,
        h11_dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        h00 * y0 + h10_dx.value() * dy0 + h01 * y1 + h11_dx.value() * dy1
    }

    #[inline]
    fn quantity_hermite_derivative_combine(
        dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        let inv_dx = 1.0 / dx.value();
        dh00_over_dt * inv_dx * y0
            + dh10_over_dt * dy0
            + dh01_over_dt * inv_dx * y1
            + dh11_over_dt * dy1
    }

    #[inline]
    fn quantity_hermite_value_is_finite(&self) -> bool {
        self.is_finite()
    }

    #[inline]
    fn quantity_hermite_derivative_is_finite(derivative: &Self::Derivative) -> bool {
        derivative.is_finite()
    }
}

impl<X, U> QuantityHermiteInterpolable<X> for Quantity<U>
where
    X: Unit,
    U: Unit + UnitDiv<X>,
    <U as UnitDiv<X>>::Output: Unit + UnitMul<X, Output = U>,
{
    type Derivative = Quantity<<U as UnitDiv<X>>::Output>;

    #[inline]
    fn quantity_hermite_combine(
        h00: f64,
        h10_dx: Quantity<X>,
        h01: f64,
        h11_dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        y0 * h00 + (dy0 * h10_dx) + y1 * h01 + (dy1 * h11_dx)
    }

    #[inline]
    fn quantity_hermite_derivative_combine(
        dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        (y0 / dx) * dh00_over_dt
            + dy0 * dh10_over_dt
            + (y1 / dx) * dh01_over_dt
            + dy1 * dh11_over_dt
    }

    #[inline]
    fn quantity_hermite_value_is_finite(&self) -> bool {
        self.value().is_finite()
    }

    #[inline]
    fn quantity_hermite_derivative_is_finite(derivative: &Self::Derivative) -> bool {
        derivative.value().is_finite()
    }
}

impl<X, C, F, L> QuantityHermiteInterpolable<X> for Position<C, F, L>
where
    X: Unit,
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
    L: LengthUnit + UnitDiv<X>,
    <L as UnitDiv<X>>::Output: Unit + UnitMul<X, Output = L>,
{
    type Derivative = Vector<F, <L as UnitDiv<X>>::Output>;

    #[inline]
    fn quantity_hermite_combine(
        _h00: f64,
        h10_dx: Quantity<X>,
        h01: f64,
        h11_dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self {
        let chord = y1 - y0;
        y0 + chord.scale(h01)
            + displacement_from_derivative(dy0, h10_dx)
            + displacement_from_derivative(dy1, h11_dx)
    }

    #[inline]
    fn quantity_hermite_derivative_combine(
        _dh00_over_dt: f64,
        dh10_over_dt: f64,
        dh01_over_dt: f64,
        dh11_over_dt: f64,
        dx: Quantity<X>,
        y0: Self,
        dy0: Self::Derivative,
        y1: Self,
        dy1: Self::Derivative,
    ) -> Self::Derivative {
        let chord = y1 - y0;
        Vector::<F, <L as UnitDiv<X>>::Output>::new(
            (chord.x() / dx) * dh01_over_dt + dy0.x() * dh10_over_dt + dy1.x() * dh11_over_dt,
            (chord.y() / dx) * dh01_over_dt + dy0.y() * dh10_over_dt + dy1.y() * dh11_over_dt,
            (chord.z() / dx) * dh01_over_dt + dy0.z() * dh10_over_dt + dy1.z() * dh11_over_dt,
        )
    }

    #[inline]
    fn quantity_hermite_value_is_finite(&self) -> bool {
        self.x().value().is_finite() && self.y().value().is_finite() && self.z().value().is_finite()
    }

    #[inline]
    fn quantity_hermite_derivative_is_finite(derivative: &Self::Derivative) -> bool {
        derivative.x().value().is_finite()
            && derivative.y().value().is_finite()
            && derivative.z().value().is_finite()
    }
}

#[inline]
fn displacement_from_derivative<X, F, L>(
    derivative: Vector<F, <L as UnitDiv<X>>::Output>,
    dx: Quantity<X>,
) -> Vector<F, L>
where
    X: Unit,
    F: ReferenceFrame,
    L: LengthUnit + UnitDiv<X>,
    <L as UnitDiv<X>>::Output: Unit + UnitMul<X, Output = L>,
{
    Vector::<F, L>::new(
        derivative.x() * dx,
        derivative.y() * dx,
        derivative.z() * dx,
    )
}

/// A typed Hermite table node with a quantity abscissa.
#[derive(Debug, Clone, PartialEq)]
pub struct QuantityHermiteNode<X, T>
where
    X: Unit,
    T: QuantityHermiteInterpolable<X>,
{
    /// Sample abscissa.
    pub x: Quantity<X>,
    /// Sample value.
    pub value: T,
    /// Sample derivative with respect to `x`.
    pub derivative: T::Derivative,
}

/// A typed Hermite table evaluation with a quantity abscissa.
#[derive(Debug, Clone, PartialEq)]
pub struct QuantityHermiteTableEvaluation<X, T>
where
    X: Unit,
    T: QuantityHermiteInterpolable<X>,
{
    /// Interpolated value.
    pub value: T,
    /// Interpolated derivative with respect to `x`.
    pub derivative: T::Derivative,
    /// Evaluated abscissa.
    pub x: Quantity<X>,
}

/// Piecewise cubic Hermite interpolation table over a typed quantity abscissa.
pub struct CubicHermiteQuantityTable<X, T>
where
    X: Unit,
    T: QuantityHermiteInterpolable<X>,
{
    samples: Vec<QuantityHermiteNode<X, T>>,
}

impl<X, T> CubicHermiteQuantityTable<X, T>
where
    X: Unit,
    T: QuantityHermiteInterpolable<X>,
{
    /// Builds a typed table from nodes sorted by strictly increasing `x`.
    pub fn new(samples: Vec<QuantityHermiteNode<X, T>>) -> Result<Self, InterpolationError> {
        validate_len(samples.len())?;
        for sample in &samples {
            if !sample.x.value().is_finite() {
                return Err(InterpolationError::NonFiniteAbscissa);
            }
            if !sample.value.quantity_hermite_value_is_finite()
                || !T::quantity_hermite_derivative_is_finite(&sample.derivative)
            {
                return Err(InterpolationError::NonFiniteValue);
            }
        }
        validate_sorted(samples.iter().map(|sample| sample.x.value()))?;
        Ok(Self { samples })
    }

    /// Returns the table samples.
    pub fn samples(&self) -> &[QuantityHermiteNode<X, T>] {
        &self.samples
    }
}

impl<X, T> CubicHermiteQuantityTable<X, T>
where
    X: Unit,
    T: QuantityHermiteInterpolable<X> + Clone,
    T::Derivative: Clone,
{
    /// Evaluates the table without extrapolation.
    pub fn evaluate(
        &self,
        x: Quantity<X>,
    ) -> Result<QuantityHermiteTableEvaluation<X, T>, InterpolationError> {
        if !x.value().is_finite() {
            return Err(InterpolationError::NonFiniteAbscissa);
        }
        let (min, max) = self.range_raw();
        let x_raw = x.value();
        if x_raw < min || x_raw > max {
            return Err(InterpolationError::OutOfRange { x: x_raw, min, max });
        }

        let segment = self.segment_index(x_raw);
        let s0 = &self.samples[segment];
        let s1 = &self.samples[segment + 1];
        if x_raw == s0.x.value() {
            return Ok(QuantityHermiteTableEvaluation {
                value: s0.value.clone(),
                derivative: s0.derivative.clone(),
                x,
            });
        }
        if x_raw == s1.x.value() {
            return Ok(QuantityHermiteTableEvaluation {
                value: s1.value.clone(),
                derivative: s1.derivative.clone(),
                x,
            });
        }

        let dx_raw = s1.x.value() - s0.x.value();
        let normalized = (x_raw - s0.x.value()) / dx_raw;
        let basis = hermite_basis(normalized, dx_raw);

        Ok(QuantityHermiteTableEvaluation {
            value: T::quantity_hermite_combine(
                basis.h00,
                Quantity::<X>::new(basis.h10_dt),
                basis.h01,
                Quantity::<X>::new(basis.h11_dt),
                s0.value.clone(),
                s0.derivative.clone(),
                s1.value.clone(),
                s1.derivative.clone(),
            ),
            derivative: T::quantity_hermite_derivative_combine(
                basis.dh00_over_dt,
                basis.dh10_over_dt,
                basis.dh01_over_dt,
                basis.dh11_over_dt,
                Quantity::<X>::new(dx_raw),
                s0.value.clone(),
                s0.derivative.clone(),
                s1.value.clone(),
                s1.derivative.clone(),
            ),
            x,
        })
    }

    fn range_raw(&self) -> (f64, f64) {
        (
            self.samples[0].x.value(),
            self.samples[self.samples.len() - 1].x.value(),
        )
    }

    fn segment_index(&self, x: f64) -> usize {
        match self
            .samples
            .binary_search_by(|sample| sample.x.value().total_cmp(&x))
        {
            Ok(index) => index.saturating_sub(1).min(self.samples.len() - 2),
            Err(index) => (index - 1).min(self.samples.len() - 2),
        }
    }
}

fn validate_len(len: usize) -> Result<(), InterpolationError> {
    if len == 0 {
        return Err(InterpolationError::EmptyTable);
    }
    if len < 2 {
        return Err(InterpolationError::TooFewSamples {
            required: 2,
            actual: len,
        });
    }
    Ok(())
}

fn validate_sorted(xs: impl IntoIterator<Item = f64>) -> Result<(), InterpolationError> {
    let mut previous = None;
    for x in xs {
        if let Some(previous) = previous {
            if x == previous {
                return Err(InterpolationError::DuplicateAbscissa);
            }
            if x < previous {
                return Err(InterpolationError::UnsortedAbscissa);
            }
        }
        previous = Some(x);
    }
    Ok(())
}
