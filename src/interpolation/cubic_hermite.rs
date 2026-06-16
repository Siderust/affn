//! Cubic Hermite interpolation tables.
//!
//! Cubic Hermite interpolation is C1 continuous when neighboring samples carry
//! consistent first derivatives. Tables never extrapolate outside their
//! abscissa coverage.
//!
//! Use typed `qtty::Quantity` abscissae for physical domains such as time,
//! length, or angle. Raw `f64` abscissae are intended only for explicitly
//! scalar interpolation, for example [`ScalarCubicHermiteTable`].
//!
//! `Position` interpolation is affine-safe: it interpolates from a segment-local
//! origin using a chord displacement and never adds two positions. Position
//! support currently requires centers with `Params = ()`; parameterized centers
//! need a future checked API.

use super::error::InterpolationError;
use super::traits::{HermiteBasis, HermiteInterpolable};
use super::InterpolationAbscissa;

/// A Hermite table node.
#[derive(Debug, Clone, PartialEq)]
pub struct HermiteNode<A, T>
where
    A: InterpolationAbscissa,
    T: HermiteInterpolable<A>,
{
    /// Sample abscissa.
    pub abscissa: A,
    /// Sample value.
    pub value: T,
    /// Sample derivative with respect to `abscissa`.
    pub derivative: T::Derivative,
}

/// A Hermite table evaluation.
#[derive(Debug, Clone, PartialEq)]
pub struct HermiteTableEvaluation<A, T>
where
    A: InterpolationAbscissa,
    T: HermiteInterpolable<A>,
{
    /// Interpolated value.
    pub value: T,
    /// Interpolated derivative with respect to `abscissa`.
    pub derivative: T::Derivative,
    /// Evaluated abscissa.
    pub abscissa: A,
}

/// Piecewise cubic Hermite interpolation table for typed values.
///
/// `A` may be a raw scalar parameter (`f64`) or a typed `qtty::Quantity` such
/// as seconds or days. Use typed quantities for physical domains so derivatives
/// carry the expected units.
pub struct CubicHermiteTable<A, T>
where
    A: InterpolationAbscissa,
    T: HermiteInterpolable<A>,
{
    samples: Vec<HermiteNode<A, T>>,
}

impl<A, T> CubicHermiteTable<A, T>
where
    A: InterpolationAbscissa,
    T: HermiteInterpolable<A>,
{
    /// Builds a typed table from nodes sorted by strictly increasing abscissa.
    pub fn new(samples: Vec<HermiteNode<A, T>>) -> Result<Self, InterpolationError> {
        validate_len(samples.len())?;
        for sample in &samples {
            if !sample.abscissa.is_finite() {
                return Err(InterpolationError::NonFiniteAbscissa);
            }
            if !sample.value.hermite_value_is_finite()
                || !T::hermite_derivative_is_finite(&sample.derivative)
            {
                return Err(InterpolationError::NonFiniteValue);
            }
        }
        validate_sorted(samples.iter().map(|sample| sample.abscissa))?;
        Ok(Self { samples })
    }

    /// Returns the table samples.
    pub fn samples(&self) -> &[HermiteNode<A, T>] {
        &self.samples
    }
}

impl<A, T> CubicHermiteTable<A, T>
where
    A: InterpolationAbscissa,
    T: HermiteInterpolable<A> + Clone,
    T::Derivative: Clone,
{
    /// Evaluates the table without extrapolation.
    pub fn evaluate(
        &self,
        abscissa: A,
    ) -> Result<HermiteTableEvaluation<A, T>, InterpolationError> {
        if !abscissa.is_finite() {
            return Err(InterpolationError::NonFiniteAbscissa);
        }
        let (min, max) = self.range();
        if abscissa.cmp_abscissa(min).is_lt() || abscissa.cmp_abscissa(max).is_gt() {
            return Err(InterpolationError::OutOfRange {
                requested_raw: abscissa.diagnostic_raw(),
                min_raw: min.diagnostic_raw(),
                max_raw: max.diagnostic_raw(),
            });
        }

        let segment = self.segment_index(abscissa);
        let s0 = &self.samples[segment];
        let s1 = &self.samples[segment + 1];
        if abscissa.cmp_abscissa(s0.abscissa).is_eq() {
            return Ok(HermiteTableEvaluation {
                value: s0.value.clone(),
                derivative: s0.derivative.clone(),
                abscissa,
            });
        }
        if abscissa.cmp_abscissa(s1.abscissa).is_eq() {
            return Ok(HermiteTableEvaluation {
                value: s1.value.clone(),
                derivative: s1.derivative.clone(),
                abscissa,
            });
        }

        let dx = s1.abscissa.delta_since(s0.abscissa);
        let tau = abscissa.normalize_between(s0.abscissa, s1.abscissa)?;
        let basis = HermiteBasis::<A>::new(tau, dx);

        Ok(HermiteTableEvaluation {
            value: T::hermite_value(
                basis,
                s0.value.clone(),
                s0.derivative.clone(),
                s1.value.clone(),
                s1.derivative.clone(),
            ),
            derivative: T::hermite_derivative(
                basis,
                s0.value.clone(),
                s0.derivative.clone(),
                s1.value.clone(),
                s1.derivative.clone(),
            ),
            abscissa,
        })
    }

    fn range(&self) -> (A, A) {
        (
            self.samples[0].abscissa,
            self.samples[self.samples.len() - 1].abscissa,
        )
    }

    fn segment_index(&self, abscissa: A) -> usize {
        match self
            .samples
            .binary_search_by(|sample| sample.abscissa.cmp_abscissa(abscissa))
        {
            Ok(index) => index.saturating_sub(1).min(self.samples.len() - 2),
            Err(index) => (index - 1).min(self.samples.len() - 2),
        }
    }
}

/// Scalar cubic Hermite table alias.
pub type ScalarCubicHermiteTable = CubicHermiteTable<f64, f64>;

/// Scalar Hermite table node alias.
pub type ScalarHermiteNode = HermiteNode<f64, f64>;

/// Scalar Hermite table evaluation alias.
pub type ScalarHermiteTableEvaluation = HermiteTableEvaluation<f64, f64>;

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

fn validate_sorted<A: InterpolationAbscissa>(
    abscissae: impl IntoIterator<Item = A>,
) -> Result<(), InterpolationError> {
    let mut previous = None;
    for abscissa in abscissae {
        if let Some(previous) = previous {
            if abscissa.cmp_abscissa(previous).is_eq() {
                return Err(InterpolationError::DuplicateAbscissa);
            }
            if abscissa.cmp_abscissa(previous).is_lt() {
                return Err(InterpolationError::UnsortedAbscissa);
            }
        }
        previous = Some(abscissa);
    }
    Ok(())
}
