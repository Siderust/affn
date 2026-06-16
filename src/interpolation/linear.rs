//! Linear interpolation helpers.

use super::error::InterpolationError;

/// Evaluates scalar linear interpolation on one segment.
pub fn linear_segment(
    x: f64,
    x0: f64,
    x1: f64,
    y0: f64,
    y1: f64,
) -> Result<f64, InterpolationError> {
    if !x.is_finite() || !x0.is_finite() || !x1.is_finite() {
        return Err(InterpolationError::NonFiniteAbscissa);
    }
    if !y0.is_finite() || !y1.is_finite() {
        return Err(InterpolationError::NonFiniteValue);
    }
    if x1 <= x0 {
        if x1 == x0 {
            return Err(InterpolationError::DuplicateAbscissa);
        }
        return Err(InterpolationError::UnsortedAbscissa);
    }
    if x < x0 || x > x1 {
        return Err(InterpolationError::OutOfRange {
            x,
            min: x0,
            max: x1,
        });
    }
    let t = (x - x0) / (x1 - x0);
    Ok((1.0 - t) * y0 + t * y1)
}
