//! Serde implementations for Cartesian Position type

use super::Position;
use crate::cartesian::xyz::XYZ;
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::{LengthUnit, Quantity};
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

/// Helper function to determine if a type is zero-sized (for skip_serializing_if)
fn is_zero_sized<T>(_: &T) -> bool {
    std::mem::size_of::<T>() == 0
}

// =============================================================================
// Position Serde Implementation
// =============================================================================

impl<C, F, U> Serialize for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    C::Params: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeStruct;

        let has_params = !is_zero_sized(self.center_params());
        let field_count = if has_params { 2 } else { 1 };

        let mut state = serializer.serialize_struct("Position", field_count)?;
        state.serialize_field("xyz", &self.xyz)?;

        // Only serialize center_params if it's not zero-sized
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
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "lowercase")]
        enum Field {
            Xyz,
            #[serde(rename = "center_params")]
            CenterParams,
        }

        struct PositionVisitor<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit>(
            PhantomData<(C, F, U)>,
        );

        impl<'de, C, F, U> serde::de::Visitor<'de> for PositionVisitor<C, F, U>
        where
            C: ReferenceCenter,
            F: ReferenceFrame,
            U: LengthUnit,
            C::Params: Deserialize<'de> + Default,
        {
            type Value = Position<C, F, U>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("struct Position")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Position<C, F, U>, V::Error>
            where
                V: serde::de::MapAccess<'de>,
            {
                let mut xyz = None;
                let mut center_params = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Xyz => {
                            if xyz.is_some() {
                                return Err(serde::de::Error::duplicate_field("xyz"));
                            }
                            xyz = Some(map.next_value()?);
                        }
                        Field::CenterParams => {
                            if center_params.is_some() {
                                return Err(serde::de::Error::duplicate_field("center_params"));
                            }
                            center_params = Some(map.next_value()?);
                        }
                    }
                }

                let xyz: XYZ<Quantity<U>> =
                    xyz.ok_or_else(|| serde::de::Error::missing_field("xyz"))?;
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
