//! Serde implementations for Ellipsoidal Position.
//!
//! Serialised format: `{"lon": …, "lat": …, "height": …}` (plus optional
//! `"center_params"` for non-ZST center parameters).  This is identical to
//! the old `GeodeticCoord` format for backward compatibility.

use super::Position;
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use crate::serde_utils::is_zero_sized;
use qtty::{Degrees, LengthUnit, Quantity};
use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize, Serializer};
use std::fmt;
use std::marker::PhantomData;

// =============================================================================
// Serialize
// =============================================================================

impl<C, F, U> Serialize for Position<C, F, U>
where
    C: ReferenceCenter,
    C::Params: Serialize,
    F: ReferenceFrame,
    U: LengthUnit,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let has_params = !is_zero_sized(&self.center_params);
        let field_count = if has_params { 4 } else { 3 };
        let mut state = serializer.serialize_struct("Position", field_count)?;
        state.serialize_field("lon", &self.lon)?;
        state.serialize_field("lat", &self.lat)?;
        state.serialize_field("height", &self.height)?;
        if has_params {
            state.serialize_field("center_params", self.center_params())?;
        }
        state.end()
    }
}

// =============================================================================
// Deserialize
// =============================================================================

impl<'de, C, F, U> Deserialize<'de> for Position<C, F, U>
where
    C: ReferenceCenter,
    C::Params: Deserialize<'de> + Default,
    F: ReferenceFrame,
    U: LengthUnit,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct EllipsoidalVisitor<C, F, U>(PhantomData<(C, F, U)>);

        impl<'de, C, F, U> Visitor<'de> for EllipsoidalVisitor<C, F, U>
        where
            C: ReferenceCenter,
            C::Params: Deserialize<'de> + Default,
            F: ReferenceFrame,
            U: LengthUnit,
        {
            type Value = Position<C, F, U>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(
                    formatter,
                    "an ellipsoidal position with 'lon', 'lat', and 'height' fields"
                )
            }

            fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
            where
                M: MapAccess<'de>,
            {
                let mut lon: Option<Degrees> = None;
                let mut lat: Option<Degrees> = None;
                let mut height: Option<Quantity<U>> = None;
                let mut center_params: Option<C::Params> = None;

                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "lon" => {
                            if lon.is_some() {
                                return Err(de::Error::duplicate_field("lon"));
                            }
                            lon = Some(map.next_value()?);
                        }
                        "lat" => {
                            if lat.is_some() {
                                return Err(de::Error::duplicate_field("lat"));
                            }
                            lat = Some(map.next_value()?);
                        }
                        "height" => {
                            if height.is_some() {
                                return Err(de::Error::duplicate_field("height"));
                            }
                            height = Some(map.next_value()?);
                        }
                        "center_params" => {
                            if center_params.is_some() {
                                return Err(de::Error::duplicate_field("center_params"));
                            }
                            center_params = Some(map.next_value()?);
                        }
                        _ => {
                            let _ = map.next_value::<de::IgnoredAny>()?;
                        }
                    }
                }

                let lon = lon.ok_or_else(|| de::Error::missing_field("lon"))?;
                let lat = lat.ok_or_else(|| de::Error::missing_field("lat"))?;
                let height = height.ok_or_else(|| de::Error::missing_field("height"))?;
                let center_params = center_params.unwrap_or_default();

                Ok(Position {
                    lon,
                    lat,
                    height,
                    center_params,
                    _frame: PhantomData,
                })
            }
        }

        deserializer.deserialize_map(EllipsoidalVisitor(PhantomData))
    }
}
