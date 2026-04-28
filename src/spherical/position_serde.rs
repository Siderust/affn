//! Serde implementations for Spherical coordinate types.

use super::Position;
use crate::centers::ReferenceCenter;
use crate::frames::SphericalNaming;
use crate::serde_utils::{collect_field, is_zero_sized, skip_unknown, take_required};
use qtty::angular::Degrees;
use qtty::length::LengthUnit;
use qtty::Quantity;
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::Serializer;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;

impl<C, F, U> Serialize for Position<C, F, U>
where
    C: ReferenceCenter,
    C::Params: Serialize,
    F: SphericalNaming,
    U: LengthUnit,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let polar_name = F::polar_name();
        let azimuth_name = F::azimuth_name();
        let distance_name = F::distance_name();
        let has_params = !is_zero_sized(&self.center_params);

        let field_count = if has_params { 4 } else { 3 };
        let mut state = serializer.serialize_struct("Position", field_count)?;
        state.serialize_field(polar_name, &self.polar)?;
        state.serialize_field(azimuth_name, &self.azimuth)?;
        state.serialize_field(distance_name, &self.distance)?;
        if has_params {
            state.serialize_field("center_params", self.center_params())?;
        }
        state.end()
    }
}

impl<'de, C, F, U> Deserialize<'de> for Position<C, F, U>
where
    C: ReferenceCenter,
    C::Params: Deserialize<'de> + Default,
    F: SphericalNaming,
    U: LengthUnit,
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct PositionVisitor<C, F, U>(PhantomData<(C, F, U)>);

        impl<'de, C, F, U> Visitor<'de> for PositionVisitor<C, F, U>
        where
            C: ReferenceCenter,
            C::Params: Deserialize<'de> + Default,
            F: SphericalNaming,
            U: LengthUnit,
        {
            type Value = Position<C, F, U>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(
                    formatter,
                    "a spherical position with '{}', '{}', and '{}' fields",
                    F::polar_name(),
                    F::azimuth_name(),
                    F::distance_name()
                )
            }

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Self::Value, M::Error> {
                let polar_name = F::polar_name();
                let azimuth_name = F::azimuth_name();
                let distance_name = F::distance_name();

                let mut polar: Option<Degrees> = None;
                let mut azimuth: Option<Degrees> = None;
                let mut distance: Option<Quantity<U>> = None;
                let mut center_params: Option<C::Params> = None;

                while let Some(key) = map.next_key::<String>()? {
                    if key == polar_name {
                        collect_field(&mut polar, polar_name, &mut map)?;
                    } else if key == azimuth_name {
                        collect_field(&mut azimuth, azimuth_name, &mut map)?;
                    } else if key == distance_name {
                        collect_field(&mut distance, distance_name, &mut map)?;
                    } else if key == "center_params" {
                        collect_field(&mut center_params, "center_params", &mut map)?;
                    } else {
                        skip_unknown(&mut map)?;
                    }
                }

                let polar = take_required(polar, polar_name)?;
                let azimuth = take_required(azimuth, azimuth_name)?;
                let distance = take_required(distance, distance_name)?;
                let center_params = center_params.unwrap_or_default();

                Ok(Position::new_with_params(
                    center_params,
                    polar,
                    azimuth,
                    distance,
                ))
            }
        }

        deserializer.deserialize_map(PositionVisitor(PhantomData))
    }
}
