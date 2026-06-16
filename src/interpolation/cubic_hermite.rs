//! Cubic Hermite interpolation tables.

use super::error::InterpolationError;
use super::scalar::{cubic_hermite_segment, hermite_basis, HermiteEvaluation};
use super::traits::HermiteInterpolable;

/// A scalar Hermite table sample.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HermiteSample {
    /// Sample abscissa.
    pub x: f64,
    /// Sample value.
    pub y: f64,
    /// Sample derivative with respect to `x`.
    pub dydx: f64,
}

/// Piecewise scalar cubic Hermite spline.
///
/// Derivative continuity is guaranteed only up to the first derivative supplied
/// at each sample. Acceleration or other second derivative quantities are not
/// generally continuous across sample boundaries.
#[derive(Debug, Clone, PartialEq)]
pub struct CubicHermiteSpline {
    samples: Vec<HermiteSample>,
}

impl CubicHermiteSpline {
    /// Builds a spline from samples sorted by strictly increasing `x`.
    pub fn new(samples: Vec<HermiteSample>) -> Result<Self, InterpolationError> {
        validate_len(samples.len())?;
        for sample in &samples {
            if !sample.x.is_finite() {
                return Err(InterpolationError::NonFiniteAbscissa);
            }
            if !sample.y.is_finite() || !sample.dydx.is_finite() {
                return Err(InterpolationError::NonFiniteValue);
            }
        }
        validate_sorted(samples.iter().map(|sample| sample.x))?;
        Ok(Self { samples })
    }

    /// Returns the table samples.
    pub fn samples(&self) -> &[HermiteSample] {
        &self.samples
    }

    /// Evaluates the spline without extrapolation.
    pub fn evaluate(&self, x: f64) -> Result<HermiteEvaluation, InterpolationError> {
        if !x.is_finite() {
            return Err(InterpolationError::NonFiniteAbscissa);
        }
        let (min, max) = self.range();
        if x < min || x > max {
            return Err(InterpolationError::OutOfRange { x, min, max });
        }

        let segment = self.segment_index(x);
        let s0 = self.samples[segment];
        let s1 = self.samples[segment + 1];
        if x == s0.x {
            return Ok(HermiteEvaluation {
                value: s0.y,
                derivative: s0.dydx,
            });
        }
        if x == s1.x {
            return Ok(HermiteEvaluation {
                value: s1.y,
                derivative: s1.dydx,
            });
        }
        cubic_hermite_segment(x, s0.x, s1.x, s0.y, s0.dydx, s1.y, s1.dydx)
    }

    fn range(&self) -> (f64, f64) {
        (self.samples[0].x, self.samples[self.samples.len() - 1].x)
    }

    fn segment_index(&self, x: f64) -> usize {
        match self
            .samples
            .binary_search_by(|sample| sample.x.total_cmp(&x))
        {
            Ok(index) => index.saturating_sub(1).min(self.samples.len() - 2),
            Err(index) => (index - 1).min(self.samples.len() - 2),
        }
    }
}

/// A typed Hermite table node.
#[derive(Debug, Clone, PartialEq)]
pub struct HermiteNode<T>
where
    T: HermiteInterpolable,
{
    /// Sample abscissa.
    pub x: f64,
    /// Sample value.
    pub value: T,
    /// Sample derivative with respect to `x`.
    pub derivative: T::Derivative,
}

/// A typed Hermite table evaluation.
#[derive(Debug, Clone, PartialEq)]
pub struct HermiteTableEvaluation<T>
where
    T: HermiteInterpolable,
{
    /// Interpolated value.
    pub value: T,
    /// Interpolated derivative with respect to `x`.
    pub derivative: T::Derivative,
}

/// Piecewise cubic Hermite interpolation table for typed values.
///
/// The abscissa is a monotonic scalar owned by the caller. For time-domain
/// ephemerides, downstream code should map epochs to a scalar such as elapsed
/// seconds before constructing this table.
///
/// Derivative continuity is guaranteed only up to the first derivative supplied
/// at each sample. Acceleration or other second derivative quantities are not
/// generally continuous across sample boundaries.
pub struct CubicHermiteTable<T>
where
    T: HermiteInterpolable,
{
    samples: Vec<HermiteNode<T>>,
}

impl<T> CubicHermiteTable<T>
where
    T: HermiteInterpolable,
{
    /// Builds a typed table from nodes sorted by strictly increasing `x`.
    pub fn new(samples: Vec<HermiteNode<T>>) -> Result<Self, InterpolationError> {
        validate_len(samples.len())?;
        for sample in &samples {
            if !sample.x.is_finite() {
                return Err(InterpolationError::NonFiniteAbscissa);
            }
            if !sample.value.hermite_value_is_finite()
                || !T::hermite_derivative_is_finite(&sample.derivative)
            {
                return Err(InterpolationError::NonFiniteValue);
            }
        }
        validate_sorted(samples.iter().map(|sample| sample.x))?;
        Ok(Self { samples })
    }

    /// Returns the table samples.
    pub fn samples(&self) -> &[HermiteNode<T>] {
        &self.samples
    }
}

impl<T> CubicHermiteTable<T>
where
    T: HermiteInterpolable + Clone,
    T::Derivative: Clone,
{
    /// Evaluates the table without extrapolation.
    pub fn evaluate(&self, x: f64) -> Result<HermiteTableEvaluation<T>, InterpolationError> {
        if !x.is_finite() {
            return Err(InterpolationError::NonFiniteAbscissa);
        }
        let (min, max) = self.range();
        if x < min || x > max {
            return Err(InterpolationError::OutOfRange { x, min, max });
        }

        let segment = self.segment_index(x);
        let s0 = &self.samples[segment];
        let s1 = &self.samples[segment + 1];
        if x == s0.x {
            return Ok(HermiteTableEvaluation {
                value: s0.value.clone(),
                derivative: s0.derivative.clone(),
            });
        }
        if x == s1.x {
            return Ok(HermiteTableEvaluation {
                value: s1.value.clone(),
                derivative: s1.derivative.clone(),
            });
        }

        let dt = s1.x - s0.x;
        let t = (x - s0.x) / dt;
        let basis = hermite_basis(t, dt);

        Ok(HermiteTableEvaluation {
            value: T::hermite_combine(
                basis.h00,
                basis.h10_dt,
                basis.h01,
                basis.h11_dt,
                s0.value.clone(),
                s0.derivative.clone(),
                s1.value.clone(),
                s1.derivative.clone(),
            ),
            derivative: T::hermite_derivative_combine(
                basis.dh00_over_dt,
                basis.dh10_over_dt,
                basis.dh01_over_dt,
                basis.dh11_over_dt,
                basis.inv_dt,
                s0.value.clone(),
                s0.derivative.clone(),
                s1.value.clone(),
                s1.derivative.clone(),
            ),
        })
    }

    fn range(&self) -> (f64, f64) {
        (self.samples[0].x, self.samples[self.samples.len() - 1].x)
    }

    fn segment_index(&self, x: f64) -> usize {
        match self
            .samples
            .binary_search_by(|sample| sample.x.total_cmp(&x))
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
