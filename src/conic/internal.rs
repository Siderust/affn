use qtty::{LengthUnit, Quantity};

use super::{ConicKind, ConicValidationError};

/// Classify eccentricity. This is only called after validation.
#[inline]
pub(super) fn classify_eccentricity_unchecked(eccentricity: f64) -> ConicKind {
    if eccentricity < 1.0 {
        ConicKind::Elliptic
    } else if eccentricity > 1.0 {
        ConicKind::Hyperbolic
    } else {
        ConicKind::Parabolic
    }
}

pub(super) fn validate_eccentricity(eccentricity: f64) -> Result<(), ConicValidationError> {
    if !eccentricity.is_finite() || eccentricity < 0.0 {
        return Err(ConicValidationError::InvalidEccentricity);
    }
    Ok(())
}

pub(super) fn validate_positive_length<U: LengthUnit>(
    value: Quantity<U>,
    error: ConicValidationError,
) -> Result<(), ConicValidationError> {
    if !value.value().is_finite() || value.value() <= 0.0 {
        return Err(error);
    }
    Ok(())
}
