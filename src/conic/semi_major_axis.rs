use std::marker::PhantomData;

use qtty::{LengthUnit, Meter, Quantity};

use super::internal::{
    classify_eccentricity_unchecked, validate_eccentricity, validate_positive_length,
};
use super::{
    sealed, ConicKind, ConicShape, ConicValidationError, Elliptic, Hyperbolic,
    NonParabolicKindMarker, PeriapsisParam, TypedPeriapsisParam,
};

/// Conic geometry expressed using semi-major axis.
///
/// Only valid for non-parabolic conics (`e != 1`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SemiMajorAxisParam<U: LengthUnit = Meter> {
    semi_major_axis: Quantity<U>,
    eccentricity: f64,
}

impl<U: LengthUnit> sealed::ConicShapeSealed for SemiMajorAxisParam<U> {}

impl<U: LengthUnit> ConicShape for SemiMajorAxisParam<U> {
    fn shape_name() -> &'static str {
        "semi_major_axis"
    }

    fn eccentricity(&self) -> f64 {
        self.eccentricity
    }

    fn kind(&self) -> ConicKind {
        classify_eccentricity_unchecked(self.eccentricity)
    }
}

impl<U: LengthUnit> SemiMajorAxisParam<U> {
    /// Constructs a validated semi-major-axis-based conic shape.
    pub fn try_new(
        semi_major_axis: Quantity<U>,
        eccentricity: f64,
    ) -> Result<Self, ConicValidationError> {
        validate_positive_length(semi_major_axis, ConicValidationError::InvalidSemiMajorAxis)?;
        validate_eccentricity(eccentricity)?;
        if eccentricity == 1.0 {
            return Err(ConicValidationError::ParabolicSemiMajorAxis);
        }
        Ok(Self {
            semi_major_axis,
            eccentricity,
        })
    }

    /// Constructs a semi-major-axis conic shape without validation.
    pub const fn new_unchecked(semi_major_axis: Quantity<U>, eccentricity: f64) -> Self {
        Self {
            semi_major_axis,
            eccentricity,
        }
    }

    /// The semi-major axis.
    #[inline]
    pub const fn semi_major_axis(&self) -> Quantity<U> {
        self.semi_major_axis
    }

    /// The orbital eccentricity.
    #[inline]
    pub const fn eccentricity(&self) -> f64 {
        self.eccentricity
    }

    /// Converts to periapsis-distance form.
    pub fn to_periapsis(&self) -> Option<PeriapsisParam<U>> {
        let e = self.eccentricity;
        let q = self.semi_major_axis.value() * (1.0 - e).abs();
        if !q.is_finite() || q <= 0.0 {
            return None;
        }
        Some(PeriapsisParam::new_unchecked(Quantity::new(q), e))
    }

    /// Classifies this shape, returning a kind-typed wrapper.
    pub fn classify(self) -> ClassifiedSemiMajorAxisParam<U> {
        match self.kind() {
            ConicKind::Elliptic => {
                ClassifiedSemiMajorAxisParam::Elliptic(TypedSemiMajorAxisParam::from_inner(self))
            }
            ConicKind::Hyperbolic => {
                ClassifiedSemiMajorAxisParam::Hyperbolic(TypedSemiMajorAxisParam::from_inner(self))
            }
            ConicKind::Parabolic => {
                unreachable!("SemiMajorAxisParam rejects e == 1 at construction")
            }
        }
    }
}

/// Result of classifying an erased `SemiMajorAxisParam`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ClassifiedSemiMajorAxisParam<U: LengthUnit = Meter> {
    /// Elliptic conic (`0 <= e < 1`).
    Elliptic(TypedSemiMajorAxisParam<U, Elliptic>),
    /// Hyperbolic conic (`e > 1`).
    Hyperbolic(TypedSemiMajorAxisParam<U, Hyperbolic>),
}

/// Semi-major-axis parameterisation branded with a non-parabolic kind `K`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TypedSemiMajorAxisParam<U: LengthUnit, K: NonParabolicKindMarker> {
    inner: SemiMajorAxisParam<U>,
    _kind: PhantomData<K>,
}

impl<U: LengthUnit, K: NonParabolicKindMarker> sealed::ConicShapeSealed
    for TypedSemiMajorAxisParam<U, K>
{
}

impl<U: LengthUnit, K: NonParabolicKindMarker> ConicShape for TypedSemiMajorAxisParam<U, K> {
    fn shape_name() -> &'static str {
        "semi_major_axis"
    }

    fn eccentricity(&self) -> f64 {
        self.inner.eccentricity()
    }

    fn kind(&self) -> ConicKind {
        K::conic_kind()
    }
}

impl<U: LengthUnit, K: NonParabolicKindMarker> TypedSemiMajorAxisParam<U, K> {
    pub(super) const fn from_inner(inner: SemiMajorAxisParam<U>) -> Self {
        Self {
            inner,
            _kind: PhantomData,
        }
    }

    /// Returns `Some` if `inner`'s eccentricity matches kind `K`, `None` otherwise.
    pub fn try_new(inner: SemiMajorAxisParam<U>) -> Option<Self> {
        if inner.kind() == K::conic_kind() {
            Some(Self {
                inner,
                _kind: PhantomData,
            })
        } else {
            None
        }
    }

    /// The semi-major axis.
    #[inline]
    pub const fn semi_major_axis(&self) -> Quantity<U> {
        self.inner.semi_major_axis()
    }

    /// The orbital eccentricity.
    #[inline]
    pub const fn eccentricity(&self) -> f64 {
        self.inner.eccentricity()
    }

    /// Returns the inner erased shape.
    #[inline]
    pub const fn into_inner(self) -> SemiMajorAxisParam<U> {
        self.inner
    }

    /// Converts to periapsis-distance form. Returns `None` if the result overflows.
    pub fn to_periapsis(&self) -> Option<TypedPeriapsisParam<U, K>> {
        self.inner
            .to_periapsis()
            .map(TypedPeriapsisParam::from_inner)
    }
}

#[cfg(feature = "serde")]
mod semi_major_axis_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    #[serde(bound = "")]
    struct SemiMajorAxisParamProxy<U: LengthUnit> {
        semi_major_axis: Quantity<U>,
        eccentricity: f64,
    }

    impl<U: LengthUnit> Serialize for SemiMajorAxisParam<U> {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            SemiMajorAxisParamProxy {
                semi_major_axis: self.semi_major_axis,
                eccentricity: self.eccentricity,
            }
            .serialize(s)
        }
    }

    impl<'de, U: LengthUnit> Deserialize<'de> for SemiMajorAxisParam<U> {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let proxy = SemiMajorAxisParamProxy::<U>::deserialize(d)?;
            SemiMajorAxisParam::try_new(proxy.semi_major_axis, proxy.eccentricity)
                .map_err(serde::de::Error::custom)
        }
    }

    impl<U: LengthUnit, K: NonParabolicKindMarker> Serialize for TypedSemiMajorAxisParam<U, K>
    where
        SemiMajorAxisParam<U>: Serialize,
    {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            self.inner.serialize(s)
        }
    }

    impl<'de, U: LengthUnit, K: NonParabolicKindMarker> Deserialize<'de>
        for TypedSemiMajorAxisParam<U, K>
    where
        SemiMajorAxisParam<U>: Deserialize<'de>,
    {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let inner = SemiMajorAxisParam::<U>::deserialize(d)?;
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
