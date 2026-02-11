//! Serde implementations for Spherical coordinate types

use super::Position;
use crate::centers::ReferenceCenter;
use crate::frames::SphericalNaming;
use qtty::{Degrees, LengthUnit, Quantity};
use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::Serializer;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;

use crate::serde_utils::is_zero_sized;

// =============================================================================
// Position Serde Implementation (with SphericalNaming)
// =============================================================================

impl<C, F, U> Serialize for Position<C, F, U>
where
    C: ReferenceCenter,
    C::Params: Serialize,
    F: SphericalNaming,
    U: LengthUnit,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
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
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
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

            fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
            where
                M: MapAccess<'de>,
            {
                let polar_name = F::polar_name();
                let azimuth_name = F::azimuth_name();
                let distance_name = F::distance_name();

                let mut polar: Option<Degrees> = None;
                let mut azimuth: Option<Degrees> = None;
                let mut distance: Option<Quantity<U>> = None;
                let mut center_params: Option<C::Params> = None;

                while let Some(key) = map.next_key::<String>()? {
                    if key == polar_name {
                        if polar.is_some() {
                            return Err(de::Error::duplicate_field(polar_name));
                        }
                        polar = Some(map.next_value()?);
                    } else if key == azimuth_name {
                        if azimuth.is_some() {
                            return Err(de::Error::duplicate_field(azimuth_name));
                        }
                        azimuth = Some(map.next_value()?);
                    } else if key == distance_name {
                        if distance.is_some() {
                            return Err(de::Error::duplicate_field(distance_name));
                        }
                        distance = Some(map.next_value()?);
                    } else if key == "center_params" {
                        if center_params.is_some() {
                            return Err(de::Error::duplicate_field("center_params"));
                        }
                        center_params = Some(map.next_value()?);
                    } else {
                        // Skip unknown fields
                        let _ = map.next_value::<de::IgnoredAny>()?;
                    }
                }

                let polar = polar.ok_or_else(|| de::Error::missing_field(polar_name))?;
                let azimuth = azimuth.ok_or_else(|| de::Error::missing_field(azimuth_name))?;
                let distance = distance.ok_or_else(|| de::Error::missing_field(distance_name))?;

                // Use default for center_params if not provided and ZST
                let center_params = center_params.unwrap_or_default();

                Ok(Position {
                    polar,
                    azimuth,
                    distance,
                    center_params,
                    _frame: PhantomData,
                })
            }
        }

        deserializer.deserialize_map(PositionVisitor(PhantomData))
    }
}
