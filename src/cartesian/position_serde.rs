//! Serde implementations for Cartesian Position type.

use super::Position;
use crate::cartesian::xyz::XYZ;
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use crate::serde_utils::{collect_field, is_zero_sized, skip_unknown, take_required};
use qtty::length::LengthUnit;
use qtty::Quantity;
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;

impl<C, F, U> Serialize for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Serialize,
{
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let has_params = !is_zero_sized(self.center_params());
        let field_count = if has_params { 2 } else { 1 };

        let mut state = serializer.serialize_struct("Position", field_count)?;
        state.serialize_field("xyz", &self.xyz)?;
        if has_params {
            state.serialize_field("center_params", self.center_params())?;
        }
        state.end()
    }
}

impl<'de, C, F, U> Deserialize<'de> for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Deserialize<'de> + Default,
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct PositionVisitor<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit>(
            PhantomData<(C, F, U)>,
        );

        impl<'de, C, F, U> Visitor<'de> for PositionVisitor<C, F, U>
        where
            C: ReferenceCenter,
            F: ReferenceFrame,
            U: LengthUnit,
            C::Params: Deserialize<'de> + Default,
        {
            type Value = Position<C, F, U>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct Position")
            }

            fn visit_map<V: MapAccess<'de>>(self, mut map: V) -> Result<Self::Value, V::Error> {
                let mut xyz: Option<XYZ<Quantity<U>>> = None;
                let mut center_params: Option<C::Params> = None;

                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "xyz" => collect_field(&mut xyz, "xyz", &mut map)?,
                        "center_params" => {
                            collect_field(&mut center_params, "center_params", &mut map)?
                        }
                        _ => skip_unknown(&mut map)?,
                    }
                }

                let xyz = take_required(xyz, "xyz")?;
                let center_params = center_params.unwrap_or_default();
                Ok(Position::from_xyz_with_params(center_params, xyz))
            }
        }

        deserializer.deserialize_struct(
            "Position",
            &["xyz", "center_params"],
            PositionVisitor(PhantomData),
        )
    }
}
