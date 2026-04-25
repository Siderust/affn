//! Internal validation and classification helpers for conic shapes.

use qtty::length::LengthUnit;
use qtty::Quantity;

use super::{ConicKind, ConicValidationError};

/// Classifies an already-validated eccentricity into its conic family.
///
/// Callers must ensure `eccentricity` is finite and non-negative before
/// invoking this helper (see [`validate_eccentricity`]).
///
/// # Floating-point boundary at e = 1.0
///
/// The comparisons use exact IEEE 754 equality (`< 1.0` / `> 1.0`), so a
/// value of exactly `1.0f64` falls into the `Parabolic` branch. Callers
/// constructing parabolic conics must pass `1.0` literally — a computed
/// value like `1.0 - f64::EPSILON` will be classified as `Elliptic`.
/// NaN and Inf are rejected by [`validate_eccentricity`] before reaching here.
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

/// Validates that `eccentricity` is finite and non-negative.
pub(super) fn validate_eccentricity(eccentricity: f64) -> Result<(), ConicValidationError> {
    if !eccentricity.is_finite() || eccentricity < 0.0 {
        return Err(ConicValidationError::InvalidEccentricity);
    }
    Ok(())
}

/// Validates that a length-like quantity is finite and strictly positive.
///
/// `error` selects the domain-specific validation error returned on failure.
pub(super) fn validate_positive_length<U: LengthUnit>(
    value: Quantity<U>,
    error: ConicValidationError,
) -> Result<(), ConicValidationError> {
    if !value.value().is_finite() || value.value() <= 0.0 {
        return Err(error);
    }
    Ok(())
}
