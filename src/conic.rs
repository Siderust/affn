//! Domain-agnostic conic geometry primitives.
//!
//! These types capture reusable geometric properties of conic sections without
//! introducing any time or propagation semantics.

use qtty::{Degrees, LengthUnit, Meter, Quantity};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// High-level conic classification derived from eccentricity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ConicKind {
    /// Elliptic orbit or conic (`0 <= e < 1`).
    Elliptic,
    /// Parabolic orbit or conic (`e == 1`).
    Parabolic,
    /// Hyperbolic orbit or conic (`e > 1`).
    Hyperbolic,
}

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
}

impl std::fmt::Display for ConicValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidEccentricity => write!(f, "invalid eccentricity"),
            Self::InvalidSemiMajorAxis => write!(f, "invalid semi-major axis"),
            Self::InvalidPeriapsisDistance => write!(f, "invalid periapsis distance"),
        }
    }
}

impl std::error::Error for ConicValidationError {}

/// Orientation of a conic in 3D space.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ConicOrientation {
    /// Inclination of the conic plane.
    pub inclination: Degrees,
    /// Longitude of the ascending node.
    pub longitude_of_ascending_node: Degrees,
    /// Argument of periapsis.
    pub argument_of_periapsis: Degrees,
}

impl ConicOrientation {
    /// Creates a new conic orientation.
    pub const fn new(
        inclination: Degrees,
        longitude_of_ascending_node: Degrees,
        argument_of_periapsis: Degrees,
    ) -> Self {
        Self {
            inclination,
            longitude_of_ascending_node,
            argument_of_periapsis,
        }
    }
}

/// Conic geometry expressed using periapsis distance.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(bound = ""))]
pub struct PeriapsisConic<U: LengthUnit = Meter> {
    /// Periapsis distance.
    pub periapsis_distance: Quantity<U>,
    /// Orbital eccentricity.
    pub eccentricity: f64,
}

impl<U: LengthUnit> PeriapsisConic<U> {
    /// Creates a new periapsis-based conic model.
    pub const fn new(periapsis_distance: Quantity<U>, eccentricity: f64) -> Self {
        Self {
            periapsis_distance,
            eccentricity,
        }
    }

    /// Classifies the conic from its eccentricity.
    pub fn kind(&self) -> Result<ConicKind, ConicValidationError> {
        classify_eccentricity(self.eccentricity)
    }

    /// Validates the conic parameters.
    pub fn validate(&self) -> Result<(), ConicValidationError> {
        validate_positive_length(
            self.periapsis_distance,
            ConicValidationError::InvalidPeriapsisDistance,
        )?;
        self.kind()?;
        Ok(())
    }
}

/// Conic geometry expressed using semi-major axis.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(bound = ""))]
pub struct SemiMajorAxisConic<U: LengthUnit = Meter> {
    /// Semi-major axis.
    pub semi_major_axis: Quantity<U>,
    /// Orbital eccentricity.
    pub eccentricity: f64,
}

impl<U: LengthUnit> SemiMajorAxisConic<U> {
    /// Creates a new semi-major-axis-based conic model.
    pub const fn new(semi_major_axis: Quantity<U>, eccentricity: f64) -> Self {
        Self {
            semi_major_axis,
            eccentricity,
        }
    }

    /// Classifies the conic from its eccentricity.
    pub fn kind(&self) -> Result<ConicKind, ConicValidationError> {
        classify_eccentricity(self.eccentricity)
    }

    /// Validates the conic parameters.
    pub fn validate(&self) -> Result<(), ConicValidationError> {
        validate_positive_length(
            self.semi_major_axis,
            ConicValidationError::InvalidSemiMajorAxis,
        )?;
        self.kind()?;
        Ok(())
    }
}

/// Periapsis-based conic geometry plus 3D orientation.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(bound = ""))]
pub struct OrientedPeriapsisConic<U: LengthUnit = Meter> {
    /// Periapsis-based conic geometry.
    pub conic: PeriapsisConic<U>,
    /// 3D orientation of the conic.
    pub orientation: ConicOrientation,
}

impl<U: LengthUnit> OrientedPeriapsisConic<U> {
    /// Creates a new oriented periapsis-based conic.
    pub const fn new(
        periapsis_distance: Quantity<U>,
        eccentricity: f64,
        orientation: ConicOrientation,
    ) -> Self {
        Self::from_parts(
            PeriapsisConic::new(periapsis_distance, eccentricity),
            orientation,
        )
    }

    /// Creates a new oriented conic from an existing shape and orientation.
    pub const fn from_parts(conic: PeriapsisConic<U>, orientation: ConicOrientation) -> Self {
        Self { conic, orientation }
    }

    /// Classifies the conic from its eccentricity.
    pub fn kind(&self) -> Result<ConicKind, ConicValidationError> {
        self.conic.kind()
    }

    /// Validates the conic parameters.
    pub fn validate(&self) -> Result<(), ConicValidationError> {
        self.conic.validate()
    }
}

/// Semi-major-axis-based conic geometry plus 3D orientation.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(bound = ""))]
pub struct OrientedSemiMajorAxisConic<U: LengthUnit = Meter> {
    /// Semi-major-axis-based conic geometry.
    pub conic: SemiMajorAxisConic<U>,
    /// 3D orientation of the conic.
    pub orientation: ConicOrientation,
}

impl<U: LengthUnit> OrientedSemiMajorAxisConic<U> {
    /// Creates a new oriented semi-major-axis-based conic.
    pub const fn new(
        semi_major_axis: Quantity<U>,
        eccentricity: f64,
        orientation: ConicOrientation,
    ) -> Self {
        Self::from_parts(
            SemiMajorAxisConic::new(semi_major_axis, eccentricity),
            orientation,
        )
    }

    /// Creates a new oriented conic from an existing shape and orientation.
    pub const fn from_parts(conic: SemiMajorAxisConic<U>, orientation: ConicOrientation) -> Self {
        Self { conic, orientation }
    }

    /// Classifies the conic from its eccentricity.
    pub fn kind(&self) -> Result<ConicKind, ConicValidationError> {
        self.conic.kind()
    }

    /// Validates the conic parameters.
    pub fn validate(&self) -> Result<(), ConicValidationError> {
        self.conic.validate()
    }
}

fn classify_eccentricity(eccentricity: f64) -> Result<ConicKind, ConicValidationError> {
    if !eccentricity.is_finite() || eccentricity < 0.0 {
        return Err(ConicValidationError::InvalidEccentricity);
    }

    if eccentricity < 1.0 {
        Ok(ConicKind::Elliptic)
    } else if eccentricity > 1.0 {
        Ok(ConicKind::Hyperbolic)
    } else {
        Ok(ConicKind::Parabolic)
    }
}

fn validate_positive_length<U: LengthUnit>(
    value: Quantity<U>,
    error: ConicValidationError,
) -> Result<(), ConicValidationError> {
    if !value.value().is_finite() || value.value() <= 0.0 {
        return Err(error);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::*;

    fn orientation() -> ConicOrientation {
        ConicOrientation::new(10.0 * DEG, 20.0 * DEG, 30.0 * DEG)
    }

    #[test]
    fn periapsis_conic_classifies_elliptic() {
        let conic = PeriapsisConic::new(1.0 * M, 0.5);
        assert_eq!(conic.kind().unwrap(), ConicKind::Elliptic);
    }

    #[test]
    fn periapsis_conic_classifies_parabolic() {
        let conic = PeriapsisConic::new(1.0 * M, 1.0);
        assert_eq!(conic.kind().unwrap(), ConicKind::Parabolic);
    }

    #[test]
    fn periapsis_conic_classifies_hyperbolic() {
        let conic = PeriapsisConic::new(1.0 * M, 1.5);
        assert_eq!(conic.kind().unwrap(), ConicKind::Hyperbolic);
    }

    #[test]
    fn negative_eccentricity_is_invalid() {
        let conic = PeriapsisConic::new(1.0 * M, -0.1);
        assert_eq!(conic.kind(), Err(ConicValidationError::InvalidEccentricity));
    }

    #[test]
    fn invalid_periapsis_distance_is_rejected() {
        let conic = PeriapsisConic::new(0.0 * M, 0.5);
        assert_eq!(
            conic.validate(),
            Err(ConicValidationError::InvalidPeriapsisDistance)
        );
    }

    #[test]
    fn invalid_semi_major_axis_is_rejected() {
        let conic = SemiMajorAxisConic::new(-1.0 * M, 0.5);
        assert_eq!(
            conic.validate(),
            Err(ConicValidationError::InvalidSemiMajorAxis)
        );
    }

    #[test]
    fn oriented_periapsis_conic_delegates_kind() {
        let conic = OrientedPeriapsisConic::new(1.0 * M, 1.5, orientation());
        assert_eq!(conic.kind().unwrap(), ConicKind::Hyperbolic);
    }

    #[test]
    fn oriented_semi_major_axis_conic_delegates_kind() {
        let conic = OrientedSemiMajorAxisConic::new(1.0 * M, 0.5, orientation());
        assert_eq!(conic.kind().unwrap(), ConicKind::Elliptic);
    }
}
