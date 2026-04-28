//! Serde implementation for Spherical Direction type.

use super::Direction;
use crate::frames::SphericalNaming;
use crate::serde_utils::{collect_field, skip_unknown, take_required};
use crate::spherical::canonicalize_polar_azimuth;
use qtty::angular::Degrees;
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};
use serde::{Deserializer, Serializer};
use std::fmt;
use std::marker::PhantomData;

impl<F: SphericalNaming> Serialize for Direction<F> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let polar_name = F::polar_name();
        let azimuth_name = F::azimuth_name();

        let mut state = serializer.serialize_struct("Direction", 2)?;
        state.serialize_field(polar_name, &self.polar)?;
        state.serialize_field(azimuth_name, &self.azimuth)?;
        state.end()
    }
}

impl<'de, F: SphericalNaming> Deserialize<'de> for Direction<F> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
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

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Self::Value, M::Error> {
                let polar_name = F::polar_name();
                let azimuth_name = F::azimuth_name();

                let mut polar: Option<Degrees> = None;
                let mut azimuth: Option<Degrees> = None;

                while let Some(key) = map.next_key::<String>()? {
                    if key == polar_name {
                        collect_field(&mut polar, polar_name, &mut map)?;
                    } else if key == azimuth_name {
                        collect_field(&mut azimuth, azimuth_name, &mut map)?;
                    } else {
                        skip_unknown(&mut map)?;
                    }
                }

                let polar = take_required(polar, polar_name)?;
                let azimuth = take_required(azimuth, azimuth_name)?;

                let (polar, azimuth) = canonicalize_polar_azimuth(polar, azimuth);
                Ok(Direction::new_unchecked(polar, azimuth))
            }
        }

        deserializer.deserialize_map(DirectionVisitor(PhantomData))
    }
}
