//! Error types for interpolation routines.

use std::fmt;

/// Errors returned by interpolation constructors and evaluators.
#[derive(Debug, Clone, PartialEq)]
pub enum InterpolationError {
    /// The interpolation table contains no samples.
    EmptyTable,
    /// The interpolation table does not contain enough samples.
    TooFewSamples {
        /// Required sample count.
        required: usize,
        /// Actual sample count.
        actual: usize,
    },
    /// An abscissa value is not finite.
    NonFiniteAbscissa,
    /// A sample value or derivative is not finite.
    NonFiniteValue,
    /// Two adjacent samples have the same abscissa.
    DuplicateAbscissa,
    /// Input samples are not sorted by increasing abscissa.
    UnsortedAbscissa,
    /// The query abscissa is outside the interpolation table range.
    OutOfRange {
        /// Query abscissa.
        x: f64,
        /// Minimum supported abscissa.
        min: f64,
        /// Maximum supported abscissa.
        max: f64,
    },
}

impl fmt::Display for InterpolationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTable => write!(f, "interpolation table is empty"),
            Self::TooFewSamples { required, actual } => write!(
                f,
                "interpolation table has too few samples: required {required}, got {actual}"
            ),
            Self::NonFiniteAbscissa => write!(f, "interpolation abscissa is not finite"),
            Self::NonFiniteValue => write!(f, "interpolation value is not finite"),
            Self::DuplicateAbscissa => {
                write!(f, "interpolation samples contain duplicate abscissae")
            }
            Self::UnsortedAbscissa => write!(f, "interpolation samples are not sorted"),
            Self::OutOfRange { x, min, max } => {
                write!(f, "interpolation query {x} is outside range [{min}, {max}]")
            }
        }
    }
}

impl std::error::Error for InterpolationError {}
