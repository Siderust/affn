//! Serde implementations for Ellipsoidal Position.
//!
//! Serialised format: `{"lon_deg": …, "lat_deg": …, "height": …}` (plus optional
//! `"center_params"` for non-ZST center parameters).  `lon_deg` and `lat_deg`
//! carry explicit degree suffixes because the fields are always `Degrees`;
//! `height` has no unit suffix because the length unit is generic (`Quantity<U>`).

use super::Position;
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use crate::serde_utils::{collect_field, is_zero_sized, skip_unknown, take_required};
use qtty::angular::Degrees;
use qtty::length::LengthUnit;
use qtty::Quantity;
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize, Serializer};
use std::fmt;
use std::marker::PhantomData;

impl<C, F, U> Serialize for Position<C, F, U>
where
    C: ReferenceCenter,
    C::Params: Serialize,
    F: ReferenceFrame,
    U: LengthUnit,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let has_params = !is_zero_sized(&self.center_params);
        let field_count = if has_params { 4 } else { 3 };
        let mut state = serializer.serialize_struct("Position", field_count)?;
        state.serialize_field("lon_deg", &self.lon)?;
        state.serialize_field("lat_deg", &self.lat)?;
        state.serialize_field("height", &self.height)?;
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
    F: ReferenceFrame,
    U: LengthUnit,
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
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
                    "an ellipsoidal position with 'lon_deg', 'lat_deg', and 'height' fields"
                )
            }

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Self::Value, M::Error> {
                let mut lon: Option<Degrees> = None;
                let mut lat: Option<Degrees> = None;
                let mut height: Option<Quantity<U>> = None;
                let mut center_params: Option<C::Params> = None;

                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "lon_deg" => collect_field(&mut lon, "lon_deg", &mut map)?,
                        "lat_deg" => collect_field(&mut lat, "lat_deg", &mut map)?,
                        "height" => collect_field(&mut height, "height", &mut map)?,
                        "center_params" => {
                            collect_field(&mut center_params, "center_params", &mut map)?
                        }
                        _ => skip_unknown(&mut map)?,
                    }
                }

                let lon = take_required(lon, "lon_deg")?;
                let lat = take_required(lat, "lat_deg")?;
                let height = take_required(height, "height")?;
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
