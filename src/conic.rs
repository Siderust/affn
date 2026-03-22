//! Domain-agnostic conic geometry primitives.
//!
//! These types capture reusable geometric properties of conic sections without
//! introducing any time or propagation semantics.
//!
//! ## Type Hierarchy
//!
//! - [`ConicShape`] – sealed trait implemented by the two canonical parameterisations.
//! - [`PeriapsisParam<U>`] – shape expressed via periapsis distance. Valid for all conic kinds.
//! - [`SemiMajorAxisParam<U>`] – shape expressed via semi-major axis. Valid for non-parabolic conics.
//! - [`ConicOrientation<F>`] – 3-D orientation tagged with a [`ReferenceFrame`].
//! - [`OrientedConic<S, F>`] – unified oriented conic, generic over shape and frame.

use std::fmt;
use std::marker::PhantomData;

use qtty::{Degrees, LengthUnit, Meter, Quantity};

use crate::frames::ReferenceFrame;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

// =============================================================================
// Sealing module
// =============================================================================

mod sealed {
    pub trait ConicShapeSealed {}
}

// =============================================================================
// Classification
// =============================================================================

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

// =============================================================================
// Validation errors
// =============================================================================

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

// =============================================================================
// ConicShape sealed trait
// =============================================================================

/// Sealed trait for the two canonical parameterisations of a conic section.
///
/// Only [`PeriapsisParam`] and [`SemiMajorAxisParam`] implement this trait.
/// It provides a uniform interface for classification and validation regardless
/// of which characteristic length is used.
pub trait ConicShape: sealed::ConicShapeSealed + Copy + Clone + fmt::Debug {
    /// Human-readable name for the characteristic length field.
    fn shape_name() -> &'static str;

    /// The orbital eccentricity stored in this shape.
    fn eccentricity(&self) -> f64;

    /// Classifies the conic from its eccentricity.
    fn kind(&self) -> Result<ConicKind, ConicValidationError>;

    /// Validates all parameters.
    fn validate(&self) -> Result<(), ConicValidationError>;
}

// =============================================================================
// PeriapsisParam<U>
// =============================================================================

/// Conic geometry expressed using periapsis distance.
///
/// Valid for all conic kinds (elliptic, parabolic, hyperbolic).
/// Replaces the old `PeriapsisConic<U>` (identical field layout).
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(bound = ""))]
pub struct PeriapsisParam<U: LengthUnit = Meter> {
    /// Periapsis distance.
    pub periapsis_distance: Quantity<U>,
    /// Orbital eccentricity.
    pub eccentricity: f64,
}

impl<U: LengthUnit> sealed::ConicShapeSealed for PeriapsisParam<U> {}

impl<U: LengthUnit> ConicShape for PeriapsisParam<U> {
    fn shape_name() -> &'static str {
        "periapsis_distance"
    }

    fn eccentricity(&self) -> f64 {
        self.eccentricity
    }

    fn kind(&self) -> Result<ConicKind, ConicValidationError> {
        classify_eccentricity(self.eccentricity)
    }

    fn validate(&self) -> Result<(), ConicValidationError> {
        validate_positive_length(
            self.periapsis_distance,
            ConicValidationError::InvalidPeriapsisDistance,
        )?;
        self.kind()?;
        Ok(())
    }
}

impl<U: LengthUnit> PeriapsisParam<U> {
    /// Creates a new periapsis-based conic shape.
    pub const fn new(periapsis_distance: Quantity<U>, eccentricity: f64) -> Self {
        Self {
            periapsis_distance,
            eccentricity,
        }
    }

    /// Converts to semi-major-axis form.
    ///
    /// Returns `None` for parabolic orbits (`e == 1`) where the semi-major axis
    /// is mathematically undefined.
    pub fn to_semi_major_axis(&self) -> Option<SemiMajorAxisParam<U>> {
        let e = self.eccentricity;
        if (e - 1.0).abs() < f64::EPSILON {
            return None;
        }
        let a = self.periapsis_distance.value() / (1.0 - e).abs();
        Some(SemiMajorAxisParam {
            semi_major_axis: Quantity::new(a),
            eccentricity: e,
        })
    }
}

// =============================================================================
// SemiMajorAxisParam<U>
// =============================================================================

/// Conic geometry expressed using semi-major axis.
///
/// Only valid for non-parabolic conics (`e ≠ 1`).
///
/// **Hyperbolic convention:** for hyperbolic conics (`e > 1`) the stored
/// `semi_major_axis` is the *positive magnitude* of the classical (negative)
/// semi-major axis, i.e. `|a|`. This matches the geometric "characteristic
/// length" interpretation (`q = a·|1 − e|`) rather than the classical
/// signed convention. All conversions to/from [`PeriapsisParam`] use
/// `abs()` accordingly.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(bound = ""))]
pub struct SemiMajorAxisParam<U: LengthUnit = Meter> {
    /// Semi-major axis.
    pub semi_major_axis: Quantity<U>,
    /// Orbital eccentricity.
    pub eccentricity: f64,
}

impl<U: LengthUnit> sealed::ConicShapeSealed for SemiMajorAxisParam<U> {}

impl<U: LengthUnit> ConicShape for SemiMajorAxisParam<U> {
    fn shape_name() -> &'static str {
        "semi_major_axis"
    }

    fn eccentricity(&self) -> f64 {
        self.eccentricity
    }

    fn kind(&self) -> Result<ConicKind, ConicValidationError> {
        classify_eccentricity(self.eccentricity)
    }

    fn validate(&self) -> Result<(), ConicValidationError> {
        validate_positive_length(
            self.semi_major_axis,
            ConicValidationError::InvalidSemiMajorAxis,
        )?;
        let kind = self.kind()?;
        if matches!(kind, ConicKind::Parabolic) {
            return Err(ConicValidationError::ParabolicSemiMajorAxis);
        }
        Ok(())
    }
}

impl<U: LengthUnit> SemiMajorAxisParam<U> {
    /// Creates a new semi-major-axis-based conic shape.
    pub const fn new(semi_major_axis: Quantity<U>, eccentricity: f64) -> Self {
        Self {
            semi_major_axis,
            eccentricity,
        }
    }

    /// Converts to periapsis-distance form. Always succeeds.
    pub fn to_periapsis(&self) -> PeriapsisParam<U> {
        let e = self.eccentricity;
        let q = self.semi_major_axis.value() * (1.0 - e).abs();
        PeriapsisParam {
            periapsis_distance: Quantity::new(q),
            eccentricity: e,
        }
    }
}

// =============================================================================
// Deprecated type aliases for old flat struct names
// =============================================================================

/// Conic geometry expressed using periapsis distance.
///
/// # Deprecated
/// Use [`PeriapsisParam`] instead.
#[deprecated(since = "0.5.0", note = "Use PeriapsisParam instead")]
pub type PeriapsisConic<U = Meter> = PeriapsisParam<U>;

/// Conic geometry expressed using semi-major axis.
///
/// # Deprecated
/// Use [`SemiMajorAxisParam`] instead.
#[deprecated(since = "0.5.0", note = "Use SemiMajorAxisParam instead")]
pub type SemiMajorAxisConic<U = Meter> = SemiMajorAxisParam<U>;

// =============================================================================
// ConicOrientation<F>
// =============================================================================

/// Orientation of a conic in 3D space within a specific reference frame.
///
/// The field names use orbital-mechanics vocabulary (inclination, ascending
/// node, periapsis) because that is the primary use case, but the type
/// itself is domain-agnostic: it represents three Euler-like angles that
/// orient a conic plane relative to a reference plane tagged by `F`.
/// Non-orbital applications may reinterpret the angles as generic tilt,
/// nodal angle, and apsidal angle.
///
/// The frame type parameter `F` prevents accidentally mixing angle sets from
/// different frames (e.g. ecliptic inclination vs. equatorial inclination)
/// at the type level.
///
/// The frame is a compile-time phantom only — no runtime data is added.
/// The serde representation is therefore identical regardless of `F`.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize), serde(bound = ""))]
pub struct ConicOrientation<F: ReferenceFrame> {
    /// Inclination of the conic plane.
    pub inclination: Degrees,
    /// Longitude of the ascending node.
    pub longitude_of_ascending_node: Degrees,
    /// Argument of periapsis.
    pub argument_of_periapsis: Degrees,
    _frame: PhantomData<F>,
}

impl<F: ReferenceFrame> ConicOrientation<F> {
    /// Creates a new conic orientation in frame `F`.
    pub const fn new(
        inclination: Degrees,
        longitude_of_ascending_node: Degrees,
        argument_of_periapsis: Degrees,
    ) -> Self {
        Self {
            inclination,
            longitude_of_ascending_node,
            argument_of_periapsis,
            _frame: PhantomData,
        }
    }

    /// Validates that all orientation angles are finite.
    pub fn validate(&self) -> Result<(), ConicValidationError> {
        if !self.inclination.value().is_finite()
            || !self.longitude_of_ascending_node.value().is_finite()
            || !self.argument_of_periapsis.value().is_finite()
        {
            return Err(ConicValidationError::InvalidOrientation);
        }
        Ok(())
    }
}

// =============================================================================
// OrientedConic<S, F>
// =============================================================================

/// A conic section with its 3-D orientation, parameterised by shape and frame.
///
/// - `S: ConicShape` — either [`PeriapsisParam<U>`] or [`SemiMajorAxisParam<U>`].
/// - `F: ReferenceFrame` — the reference frame in which the orientation angles
///   are expressed (e.g. `EclipticMeanJ2000`).
///
/// Replaces the old `OrientedPeriapsisConic<U>` and `OrientedSemiMajorAxisConic<U>`
/// with a single unified generic.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "S: Serialize, F: ReferenceFrame",
        deserialize = "S: Deserialize<'de>, F: ReferenceFrame",
    ))
)]
pub struct OrientedConic<S: ConicShape, F: ReferenceFrame> {
    /// The shape (characteristic length + eccentricity).
    pub shape: S,
    /// The 3-D orientation in frame `F`.
    pub orientation: ConicOrientation<F>,
}

impl<S: ConicShape, F: ReferenceFrame> OrientedConic<S, F> {
    /// Creates a new oriented conic from a shape and orientation.
    pub const fn new(shape: S, orientation: ConicOrientation<F>) -> Self {
        Self { shape, orientation }
    }

    /// Classifies the conic from its eccentricity.
    pub fn kind(&self) -> Result<ConicKind, ConicValidationError> {
        self.shape.kind()
    }

    /// Validates all parameters (shape and orientation).
    pub fn validate(&self) -> Result<(), ConicValidationError> {
        self.shape.validate()?;
        self.orientation.validate()
    }
}

// Conversion: PeriapsisParam → SemiMajorAxisParam (preserving orientation and frame)
impl<U: LengthUnit, F: ReferenceFrame> OrientedConic<PeriapsisParam<U>, F> {
    /// Converts to semi-major-axis form, preserving the orientation and frame.
    ///
    /// Returns `None` for parabolic orbits where the semi-major axis is undefined.
    pub fn to_semi_major_axis(&self) -> Option<OrientedConic<SemiMajorAxisParam<U>, F>> {
        self.shape.to_semi_major_axis().map(|sma| OrientedConic {
            shape: sma,
            orientation: self.orientation,
        })
    }
}

// Conversion: SemiMajorAxisParam → PeriapsisParam (preserving orientation and frame)
impl<U: LengthUnit, F: ReferenceFrame> OrientedConic<SemiMajorAxisParam<U>, F> {
    /// Converts to periapsis-distance form, preserving the orientation and frame.
    ///
    /// Always succeeds.
    pub fn to_periapsis(&self) -> OrientedConic<PeriapsisParam<U>, F> {
        OrientedConic {
            shape: self.shape.to_periapsis(),
            orientation: self.orientation,
        }
    }
}

// =============================================================================
// Deprecated oriented type aliases (gated on astro feature)
// =============================================================================

/// Periapsis-based conic geometry plus 3D orientation in `EclipticMeanJ2000`.
///
/// # Deprecated
/// Use `OrientedConic<PeriapsisParam<U>, F>` instead.
#[cfg(feature = "astro")]
#[deprecated(
    since = "0.5.0",
    note = "Use OrientedConic<PeriapsisParam<U>, F> instead"
)]
pub type OrientedPeriapsisConic<U = Meter> =
    OrientedConic<PeriapsisParam<U>, crate::frames::EclipticMeanJ2000>;

/// Semi-major-axis-based conic geometry plus 3D orientation in `EclipticMeanJ2000`.
///
/// # Deprecated
/// Use `OrientedConic<SemiMajorAxisParam<U>, F>` instead.
#[cfg(feature = "astro")]
#[deprecated(
    since = "0.5.0",
    note = "Use OrientedConic<SemiMajorAxisParam<U>, F> instead"
)]
pub type OrientedSemiMajorAxisConic<U = Meter> =
    OrientedConic<SemiMajorAxisParam<U>, crate::frames::EclipticMeanJ2000>;

// =============================================================================
// Private helpers
// =============================================================================

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

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use qtty::*;

    // Helper frame for tests (no astro feature needed)
    #[derive(Debug, Copy, Clone, PartialEq)]
    struct TestFrame;
    impl crate::frames::ReferenceFrame for TestFrame {
        fn frame_name() -> &'static str {
            "TestFrame"
        }
    }

    fn orientation() -> ConicOrientation<TestFrame> {
        ConicOrientation::new(10.0 * DEG, 20.0 * DEG, 30.0 * DEG)
    }

    #[test]
    fn periapsis_param_classifies_elliptic() {
        let shape = PeriapsisParam::new(1.0 * M, 0.5);
        assert_eq!(shape.kind().unwrap(), ConicKind::Elliptic);
    }

    #[test]
    fn periapsis_param_classifies_parabolic() {
        let shape = PeriapsisParam::new(1.0 * M, 1.0);
        assert_eq!(shape.kind().unwrap(), ConicKind::Parabolic);
    }

    #[test]
    fn periapsis_param_classifies_hyperbolic() {
        let shape = PeriapsisParam::new(1.0 * M, 1.5);
        assert_eq!(shape.kind().unwrap(), ConicKind::Hyperbolic);
    }

    #[test]
    fn negative_eccentricity_is_invalid() {
        let shape = PeriapsisParam::new(1.0 * M, -0.1);
        assert_eq!(shape.kind(), Err(ConicValidationError::InvalidEccentricity));
    }

    #[test]
    fn invalid_periapsis_distance_is_rejected() {
        let shape = PeriapsisParam::new(0.0 * M, 0.5);
        assert_eq!(
            shape.validate(),
            Err(ConicValidationError::InvalidPeriapsisDistance)
        );
    }

    #[test]
    fn invalid_semi_major_axis_is_rejected() {
        let shape = SemiMajorAxisParam::new(-1.0 * M, 0.5);
        assert_eq!(
            shape.validate(),
            Err(ConicValidationError::InvalidSemiMajorAxis)
        );
    }

    #[test]
    fn oriented_conic_periapsis_delegates_kind() {
        let conic = OrientedConic::new(PeriapsisParam::new(1.0 * M, 1.5), orientation());
        assert_eq!(conic.kind().unwrap(), ConicKind::Hyperbolic);
    }

    #[test]
    fn oriented_conic_semi_major_axis_delegates_kind() {
        let conic = OrientedConic::new(SemiMajorAxisParam::new(1.0 * M, 0.5), orientation());
        assert_eq!(conic.kind().unwrap(), ConicKind::Elliptic);
    }

    #[test]
    fn periapsis_to_semi_major_axis_elliptic() {
        let shape = PeriapsisParam::new(1.0 * M, 0.5); // q = 1, e = 0.5 → a = q/(1-e) = 2
        let sma = shape.to_semi_major_axis().unwrap();
        assert!((sma.semi_major_axis.value() - 2.0).abs() < 1e-12);
        assert_eq!(sma.eccentricity, 0.5);
    }

    #[test]
    fn periapsis_to_semi_major_axis_hyperbolic() {
        let shape = PeriapsisParam::new(1.0 * M, 2.0); // q = 1, e = 2 → a = q/|1-e| = 1
        let sma = shape.to_semi_major_axis().unwrap();
        assert!((sma.semi_major_axis.value() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn periapsis_to_semi_major_axis_parabolic_returns_none() {
        let shape = PeriapsisParam::new(1.0 * M, 1.0);
        assert!(shape.to_semi_major_axis().is_none());
    }

    #[test]
    fn semi_major_axis_to_periapsis() {
        let shape = SemiMajorAxisParam::new(2.0 * M, 0.5); // a = 2, e = 0.5 → q = a*(1-e) = 1
        let peri = shape.to_periapsis();
        assert!((peri.periapsis_distance.value() - 1.0).abs() < 1e-12);
        assert_eq!(peri.eccentricity, 0.5);
    }

    #[test]
    fn oriented_conic_conversion_preserves_orientation() {
        let ori = orientation();
        let conic: OrientedConic<PeriapsisParam<Meter>, TestFrame> =
            OrientedConic::new(PeriapsisParam::new(1.0 * M, 0.5), ori);
        let converted = conic.to_semi_major_axis().unwrap();
        assert_eq!(converted.orientation, ori);
    }

    #[test]
    fn oriented_conic_sma_to_periapsis_preserves_orientation() {
        let ori = orientation();
        let conic: OrientedConic<SemiMajorAxisParam<Meter>, TestFrame> =
            OrientedConic::new(SemiMajorAxisParam::new(2.0 * M, 0.5), ori);
        let converted = conic.to_periapsis();
        assert_eq!(converted.orientation, ori);
    }

    #[test]
    fn semi_major_axis_parabolic_is_rejected() {
        let shape = SemiMajorAxisParam::new(1.0 * M, 1.0);
        assert_eq!(
            shape.validate(),
            Err(ConicValidationError::ParabolicSemiMajorAxis)
        );
    }

    #[test]
    fn orientation_nan_is_rejected() {
        let ori = ConicOrientation::<TestFrame>::new(
            Degrees::new(f64::NAN),
            Degrees::new(0.0),
            Degrees::new(0.0),
        );
        assert_eq!(
            ori.validate(),
            Err(ConicValidationError::InvalidOrientation)
        );
    }

    #[test]
    fn orientation_infinity_is_rejected() {
        let ori = ConicOrientation::<TestFrame>::new(
            Degrees::new(0.0),
            Degrees::new(f64::INFINITY),
            Degrees::new(0.0),
        );
        assert_eq!(
            ori.validate(),
            Err(ConicValidationError::InvalidOrientation)
        );
    }

    #[test]
    fn valid_orientation_passes() {
        let ori = orientation();
        assert_eq!(ori.validate(), Ok(()));
    }

    #[test]
    fn oriented_conic_validates_orientation() {
        let bad_ori = ConicOrientation::<TestFrame>::new(
            Degrees::new(f64::NAN),
            Degrees::new(0.0),
            Degrees::new(0.0),
        );
        let conic = OrientedConic::new(PeriapsisParam::new(1.0 * M, 0.5), bad_ori);
        assert_eq!(
            conic.validate(),
            Err(ConicValidationError::InvalidOrientation)
        );
    }
}
