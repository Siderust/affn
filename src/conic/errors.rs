use std::fmt;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Validation errors for conic geometry models.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ConicValidationError {
    /// Eccentricity must be finite and non-negative.
    InvalidEccentricity,
    /// Semi-major axis must be finite and strictly positive.
    InvalidSemiMajorAxis,
    /// Periapsis distance must be finite and strictly positive.
    InvalidPeriapsisDistance,
    /// Semi-major axis is undefined for parabolic conics (`e == 1`).
    ParabolicSemiMajorAxis,
    /// Orientation angles must be finite.
    InvalidOrientation,
}

impl fmt::Display for ConicValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidEccentricity => write!(f, "invalid eccentricity"),
            Self::InvalidSemiMajorAxis => write!(f, "invalid semi-major axis"),
            Self::InvalidPeriapsisDistance => write!(f, "invalid periapsis distance"),
            Self::ParabolicSemiMajorAxis => {
                write!(
                    f,
                    "semi-major axis is undefined for parabolic conics (e == 1)"
                )
            }
            Self::InvalidOrientation => write!(f, "orientation angles must be finite"),
        }
    }
}

impl std::error::Error for ConicValidationError {}
