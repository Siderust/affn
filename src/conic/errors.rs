//! Validation errors produced by conic constructors and conversions.

use std::fmt;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Validation errors for conic geometry models.
#[derive(Clone, Copy, Debug, PartialEq)]
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
    /// A strict orientation constructor received an angle outside its canonical range.
    ///
    /// `field` identifies the offending angle (`"inclination"`,
    /// `"longitude_of_ascending_node"`, or `"argument_of_periapsis"`).
    /// `value` is the rejected value, in degrees.
    OutOfRange {
        /// Name of the angle field that was out of range.
        field: &'static str,
        /// The rejected value, expressed in degrees.
        value: f64,
    },
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
            Self::OutOfRange { field, value } => {
                write!(f, "orientation angle `{field}` is out of canonical range: {value}°")
            }
        }
    }
}

impl std::error::Error for ConicValidationError {}
