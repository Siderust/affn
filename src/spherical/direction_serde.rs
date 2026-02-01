//! Serde implementation for Spherical Direction type

use super::Direction;
use crate::frames::SphericalNaming;
use qtty::Degrees;
use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};
use serde::{Deserializer, Serializer};
use std::fmt;
use std::marker::PhantomData;

impl<F: SphericalNaming> Serialize for Direction<F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let polar_name = F::polar_name();
        let azimuth_name = F::azimuth_name();

        let mut state = serializer.serialize_struct("Direction", 2)?;
        state.serialize_field(polar_name, &self.polar)?;
        state.serialize_field(azimuth_name, &self.azimuth)?;
        state.end()
    }
}

impl<'de, F: SphericalNaming> Deserialize<'de> for Direction<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct DirectionVisitor<F>(PhantomData<F>);

        impl<'de, F: SphericalNaming> Visitor<'de> for DirectionVisitor<F> {
            type Value = Direction<F>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(
                    formatter,
                    "a spherical direction with '{}' and '{}' fields",
                    F::polar_name(),
                    F::azimuth_name()
                )
            }

            fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
            where
                M: MapAccess<'de>,
            {
                let polar_name = F::polar_name();
                let azimuth_name = F::azimuth_name();

                let mut polar: Option<Degrees> = None;
                let mut azimuth: Option<Degrees> = None;

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
                    } else {
                        // Skip unknown fields
                        let _ = map.next_value::<de::IgnoredAny>()?;
                    }
                }

                let polar = polar.ok_or_else(|| de::Error::missing_field(polar_name))?;
                let azimuth = azimuth.ok_or_else(|| de::Error::missing_field(azimuth_name))?;

                Ok(Direction::new_raw(polar, azimuth))
            }
        }

        deserializer.deserialize_map(DirectionVisitor(PhantomData))
    }
}
