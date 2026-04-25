//! Orientation-preserving wrappers that pair a conic shape with a frame tag.

use qtty::length::LengthUnit;

use crate::frames::ReferenceFrame;

use super::Elliptic;
use super::{
    ConicKind, ConicOrientation, ConicShape, Hyperbolic, NonParabolicKindMarker, PeriapsisParam,
    SemiMajorAxisParam, TypedPeriapsisParam, TypedSemiMajorAxisParam,
};

/// A conic section with its 3-D orientation, parameterised by shape and frame.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct OrientedConic<S: ConicShape, F: ReferenceFrame> {
    shape: S,
    orientation: ConicOrientation<F>,
}

impl<S: ConicShape, F: ReferenceFrame> OrientedConic<S, F> {
    /// Creates a new oriented conic from an already-validated shape and orientation.
    ///
    /// This constructor performs no extra checks; it simply packages the two
    /// validated components together.
    pub const fn new(shape: S, orientation: ConicOrientation<F>) -> Self {
        Self { shape, orientation }
    }

    /// Returns the stored shape component.
    #[inline]
    pub const fn shape(&self) -> &S {
        &self.shape
    }

    /// Returns the stored 3-D orientation in frame `F`.
    #[inline]
    pub const fn orientation(&self) -> &ConicOrientation<F> {
        &self.orientation
    }

    /// Returns the conic family derived from the underlying shape.
    #[inline]
    pub fn kind(&self) -> ConicKind {
        self.shape.kind()
    }
}

#[cfg(feature = "serde")]
mod oriented_conic_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    impl<S, F> Serialize for OrientedConic<S, F>
    where
        S: ConicShape + Serialize,
        F: ReferenceFrame,
    {
        fn serialize<Ser: Serializer>(&self, s: Ser) -> Result<Ser::Ok, Ser::Error> {
            use serde::ser::SerializeStruct;
            let mut state = s.serialize_struct("OrientedConic", 2)?;
            state.serialize_field("shape", &self.shape)?;
            state.serialize_field("orientation", &self.orientation)?;
            state.end()
        }
    }

    impl<'de, S, F> Deserialize<'de> for OrientedConic<S, F>
    where
        S: ConicShape + Deserialize<'de>,
        F: ReferenceFrame,
    {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            use serde::de::{MapAccess, Visitor};
            use std::fmt;
            use std::marker::PhantomData;

            struct OrientedConicVisitor<S: ConicShape, F: ReferenceFrame>(PhantomData<(S, F)>);

            impl<'de, S, F> Visitor<'de> for OrientedConicVisitor<S, F>
            where
                S: ConicShape + Deserialize<'de>,
                F: ReferenceFrame,
            {
                type Value = OrientedConic<S, F>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str("an OrientedConic with shape and orientation fields")
                }

                fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                    let mut shape: Option<S> = None;
                    let mut orientation: Option<ConicOrientation<F>> = None;

                    while let Some(key) = map.next_key::<String>()? {
                        match key.as_str() {
                            "shape" => {
                                shape = Some(map.next_value()?);
                            }
                            "orientation" => {
                                orientation = Some(map.next_value()?);
                            }
                            _ => {
                                map.next_value::<serde::de::IgnoredAny>()?;
                            }
                        }
                    }
                    let shape = shape.ok_or_else(|| serde::de::Error::missing_field("shape"))?;
                    let orientation = orientation
                        .ok_or_else(|| serde::de::Error::missing_field("orientation"))?;
                    Ok(OrientedConic::new(shape, orientation))
                }
            }

            d.deserialize_map(OrientedConicVisitor::<S, F>(PhantomData))
        }
    }
}

impl<U: LengthUnit, F: ReferenceFrame> OrientedConic<PeriapsisParam<U>, F> {
    /// Converts to semi-major-axis form, preserving orientation and frame.
    ///
    /// Returns `None` for parabolic shapes and for any non-finite converted
    /// semi-major axis.
    pub fn to_semi_major_axis(&self) -> Option<OrientedConic<SemiMajorAxisParam<U>, F>> {
        self.shape
            .to_semi_major_axis()
            .map(|sma| OrientedConic::new(sma, self.orientation))
    }
}

impl<U: LengthUnit, F: ReferenceFrame> OrientedConic<SemiMajorAxisParam<U>, F> {
    /// Converts to periapsis-distance form, preserving orientation and frame.
    ///
    /// Returns `None` if the derived periapsis distance overflows or becomes
    /// non-finite.
    pub fn to_periapsis(&self) -> Option<OrientedConic<PeriapsisParam<U>, F>> {
        self.shape
            .to_periapsis()
            .map(|peri| OrientedConic::new(peri, self.orientation))
    }
}

impl<U: LengthUnit, F: ReferenceFrame> OrientedConic<TypedPeriapsisParam<U, Elliptic>, F> {
    /// Converts to elliptic semi-major-axis form, preserving orientation and frame.
    ///
    /// Returns `None` if the derived semi-major axis overflows or becomes
    /// non-finite.
    pub fn to_semi_major_axis(
        &self,
    ) -> Option<OrientedConic<TypedSemiMajorAxisParam<U, Elliptic>, F>> {
        self.shape
            .to_semi_major_axis()
            .map(|sma| OrientedConic::new(sma, *self.orientation()))
    }
}

impl<U: LengthUnit, F: ReferenceFrame> OrientedConic<TypedPeriapsisParam<U, Hyperbolic>, F> {
    /// Converts to hyperbolic semi-major-axis form, preserving orientation and frame.
    ///
    /// Returns `None` if the derived semi-major axis overflows or becomes
    /// non-finite.
    pub fn to_semi_major_axis(
        &self,
    ) -> Option<OrientedConic<TypedSemiMajorAxisParam<U, Hyperbolic>, F>> {
        self.shape
            .to_semi_major_axis()
            .map(|sma| OrientedConic::new(sma, *self.orientation()))
    }
}

impl<U: LengthUnit, K: NonParabolicKindMarker, F: ReferenceFrame>
    OrientedConic<TypedSemiMajorAxisParam<U, K>, F>
{
    /// Converts to periapsis-distance form, preserving orientation and frame.
    ///
    /// Returns `None` if the derived periapsis distance overflows or becomes
    /// non-finite.
    pub fn to_periapsis(&self) -> Option<OrientedConic<TypedPeriapsisParam<U, K>, F>> {
        self.shape
            .to_periapsis()
            .map(|peri| OrientedConic::new(peri, *self.orientation()))
    }
}
