//! Scalar interpolation primitives.

use super::error::InterpolationError;

/// Scalar Hermite interpolation result.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HermiteEvaluation {
    /// Interpolated value.
    pub value: f64,
    /// Derivative with respect to the original abscissa.
    pub derivative: f64,
}

/// Evaluates one scalar cubic Hermite segment.
///
/// The returned derivative is with respect to `x`, not normalized `t`.
pub fn cubic_hermite_segment(
    x: f64,
    x0: f64,
    x1: f64,
    y0: f64,
    dy0: f64,
    y1: f64,
    dy1: f64,
) -> Result<HermiteEvaluation, InterpolationError> {
    if !x.is_finite() || !x0.is_finite() || !x1.is_finite() {
        return Err(InterpolationError::NonFiniteAbscissa);
    }
    if !y0.is_finite() || !dy0.is_finite() || !y1.is_finite() || !dy1.is_finite() {
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

    let dt = x1 - x0;
    let t = (x - x0) / dt;
    let basis = hermite_basis(t, dt);

    Ok(HermiteEvaluation {
        value: basis.h00 * y0 + basis.h10_dt * dy0 + basis.h01 * y1 + basis.h11_dt * dy1,
        derivative: basis.dh00_over_dt * basis.inv_dt * y0
            + basis.dh10_over_dt * dy0
            + basis.dh01_over_dt * basis.inv_dt * y1
            + basis.dh11_over_dt * dy1,
    })
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct HermiteBasis {
    pub h00: f64,
    pub h10_dt: f64,
    pub h01: f64,
    pub h11_dt: f64,
    pub dh00_over_dt: f64,
    pub dh10_over_dt: f64,
    pub dh01_over_dt: f64,
    pub dh11_over_dt: f64,
    pub inv_dt: f64,
}

pub(crate) fn hermite_basis(t: f64, dt: f64) -> HermiteBasis {
    let t2 = t * t;
    let t3 = t2 * t;

    HermiteBasis {
        h00: 2.0 * t3 - 3.0 * t2 + 1.0,
        h10_dt: (t3 - 2.0 * t2 + t) * dt,
        h01: -2.0 * t3 + 3.0 * t2,
        h11_dt: (t3 - t2) * dt,
        dh00_over_dt: 6.0 * t2 - 6.0 * t,
        dh10_over_dt: 3.0 * t2 - 4.0 * t + 1.0,
        dh01_over_dt: -6.0 * t2 + 6.0 * t,
        dh11_over_dt: 3.0 * t2 - 2.0 * t,
        inv_dt: 1.0 / dt,
    }
}
