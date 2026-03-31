//! Periapsis-based conic parameterisations and typed classification wrappers.

use std::marker::PhantomData;

use qtty::{LengthUnit, Meter, Quantity};

use super::internal::{
    classify_eccentricity_unchecked, validate_eccentricity, validate_positive_length,
};
use super::{
    sealed, ConicKind, ConicShape, ConicValidationError, Elliptic, Hyperbolic, KindMarker,
    Parabolic, SemiMajorAxisParam, TypedSemiMajorAxisParam,
};

/// Conic geometry expressed using periapsis distance.
///
/// Valid for all conic kinds (elliptic, parabolic, hyperbolic).
///
/// Construct via `try_new`. The fields are private; use accessors.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct PeriapsisParam<U: LengthUnit = Meter> {
    periapsis_distance: Quantity<U>,
    eccentricity: f64,
}

impl<U: LengthUnit> sealed::ConicShapeSealed for PeriapsisParam<U> {}

impl<U: LengthUnit> ConicShape for PeriapsisParam<U> {
    fn shape_name() -> &'static str {
        "periapsis_distance"
    }

    fn eccentricity(&self) -> f64 {
        self.eccentricity
    }

    fn kind(&self) -> ConicKind {
        classify_eccentricity_unchecked(self.eccentricity)
    }
}

impl<U: LengthUnit> PeriapsisParam<U> {
    /// Constructs a validated periapsis-based conic shape.
    ///
    /// `periapsis_distance` must be finite and strictly positive, and
    /// `eccentricity` must be finite and non-negative.
    pub fn try_new(
        periapsis_distance: Quantity<U>,
        eccentricity: f64,
    ) -> Result<Self, ConicValidationError> {
        validate_positive_length(
            periapsis_distance,
            ConicValidationError::InvalidPeriapsisDistance,
        )?;
        validate_eccentricity(eccentricity)?;
        Ok(Self {
            periapsis_distance,
            eccentricity,
        })
    }

    /// Constructs a periapsis-based conic shape without validation.
    ///
    /// The caller must ensure the same invariants enforced by
    /// [`try_new`](Self::try_new).
    pub const fn new_unchecked(periapsis_distance: Quantity<U>, eccentricity: f64) -> Self {
        Self {
            periapsis_distance,
            eccentricity,
        }
    }

    /// The periapsis distance.
    #[inline]
    pub const fn periapsis_distance(&self) -> Quantity<U> {
        self.periapsis_distance
    }

    /// The orbital eccentricity.
    #[inline]
    pub const fn eccentricity(&self) -> f64 {
        self.eccentricity
    }

    /// Converts to semi-major-axis form using `a = q / |1 - e|`.
    ///
    /// Returns `None` for parabolic shapes (`e == 1`) and for any non-finite or
    /// non-positive derived semi-major axis.
    pub fn to_semi_major_axis(&self) -> Option<SemiMajorAxisParam<U>> {
        let e = self.eccentricity;
        if e == 1.0 {
            return None;
        }
        let a = self.periapsis_distance.value() / (1.0 - e).abs();
        if !a.is_finite() || a <= 0.0 {
            return None;
        }
        Some(SemiMajorAxisParam::new_unchecked(Quantity::new(a), e))
    }

    /// Classifies this shape, returning a kind-typed wrapper with identical data.
    pub fn classify(self) -> ClassifiedPeriapsisParam<U> {
        match self.kind() {
            ConicKind::Elliptic => {
                ClassifiedPeriapsisParam::Elliptic(TypedPeriapsisParam::from_inner(self))
            }
            ConicKind::Parabolic => {
                ClassifiedPeriapsisParam::Parabolic(TypedPeriapsisParam::from_inner(self))
            }
            ConicKind::Hyperbolic => {
                ClassifiedPeriapsisParam::Hyperbolic(TypedPeriapsisParam::from_inner(self))
            }
        }
    }
}

/// Result of classifying an erased `PeriapsisParam`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ClassifiedPeriapsisParam<U: LengthUnit = Meter> {
    /// Elliptic conic (`0 <= e < 1`).
    Elliptic(TypedPeriapsisParam<U, Elliptic>),
    /// Parabolic conic (`e == 1`).
    Parabolic(TypedPeriapsisParam<U, Parabolic>),
    /// Hyperbolic conic (`e > 1`).
    Hyperbolic(TypedPeriapsisParam<U, Hyperbolic>),
}

/// Periapsis-distance parameterisation branded with a specific conic kind `K`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TypedPeriapsisParam<U: LengthUnit, K: KindMarker> {
    inner: PeriapsisParam<U>,
    _kind: PhantomData<K>,
}

impl<U: LengthUnit, K: KindMarker> sealed::ConicShapeSealed for TypedPeriapsisParam<U, K> {}

impl<U: LengthUnit, K: KindMarker> ConicShape for TypedPeriapsisParam<U, K> {
    fn shape_name() -> &'static str {
        "periapsis_distance"
    }

    fn eccentricity(&self) -> f64 {
        self.inner.eccentricity()
    }

    fn kind(&self) -> ConicKind {
        K::conic_kind()
    }
}

impl<U: LengthUnit, K: KindMarker> TypedPeriapsisParam<U, K> {
    /// Wraps an erased periapsis shape that is already known to match `K`.
    pub(super) const fn from_inner(inner: PeriapsisParam<U>) -> Self {
        Self {
            inner,
            _kind: PhantomData,
        }
    }

    /// The periapsis distance.
    #[inline]
    pub const fn periapsis_distance(&self) -> Quantity<U> {
        self.inner.periapsis_distance()
    }

    /// The orbital eccentricity.
    #[inline]
    pub const fn eccentricity(&self) -> f64 {
        self.inner.eccentricity()
    }

    /// Returns the inner erased shape, dropping the compile-time kind marker.
    #[inline]
    pub const fn into_inner(self) -> PeriapsisParam<U> {
        self.inner
    }
}

impl<U: LengthUnit> TypedPeriapsisParam<U, Elliptic> {
    /// Converts to elliptic semi-major-axis form.
    ///
    /// Returns `None` if the derived semi-major axis overflows or becomes
    /// non-finite.
    pub fn to_semi_major_axis(&self) -> Option<TypedSemiMajorAxisParam<U, Elliptic>> {
        self.inner
            .to_semi_major_axis()
            .map(TypedSemiMajorAxisParam::from_inner)
    }
}

impl<U: LengthUnit> TypedPeriapsisParam<U, Hyperbolic> {
    /// Converts to hyperbolic semi-major-axis form.
    ///
    /// Returns `None` if the derived semi-major axis overflows or becomes
    /// non-finite.
    pub fn to_semi_major_axis(&self) -> Option<TypedSemiMajorAxisParam<U, Hyperbolic>> {
        self.inner
            .to_semi_major_axis()
            .map(TypedSemiMajorAxisParam::from_inner)
    }
}

#[cfg(feature = "serde")]
mod periapsis_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    #[serde(bound = "")]
    struct PeriapsisParamProxy<U: LengthUnit> {
        periapsis_distance: Quantity<U>,
        eccentricity: f64,
    }

    impl<U: LengthUnit> Serialize for PeriapsisParam<U> {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            PeriapsisParamProxy {
                periapsis_distance: self.periapsis_distance,
                eccentricity: self.eccentricity,
            }
            .serialize(s)
        }
    }

    impl<'de, U: LengthUnit> Deserialize<'de> for PeriapsisParam<U> {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let proxy = PeriapsisParamProxy::<U>::deserialize(d)?;
            PeriapsisParam::try_new(proxy.periapsis_distance, proxy.eccentricity)
                .map_err(serde::de::Error::custom)
        }
    }

    impl<U: LengthUnit, K: KindMarker> Serialize for TypedPeriapsisParam<U, K>
    where
        PeriapsisParam<U>: Serialize,
    {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            self.inner.serialize(s)
        }
    }

    impl<'de, U: LengthUnit, K: KindMarker> Deserialize<'de> for TypedPeriapsisParam<U, K>
    where
        PeriapsisParam<U>: Deserialize<'de>,
    {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let inner = PeriapsisParam::<U>::deserialize(d)?;
            if inner.kind() != K::conic_kind() {
                return Err(serde::de::Error::custom(
                    "eccentricity does not match the expected conic kind",
                ));
            }
            Ok(Self {
                inner,
                _kind: PhantomData,
            })
        }
    }
}
