//! Serde implementations for Cartesian Vector type

use super::Vector;
use crate::cartesian::xyz::XYZ;
use crate::frames::ReferenceFrame;
use qtty::{Quantity, Unit};
use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;

impl<F: ReferenceFrame, U: Unit> Serialize for Vector<F, U> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Vector", 1)?;
        state.serialize_field("xyz", &self.xyz)?;
        state.end()
    }
}

impl<'de, F: ReferenceFrame, U: Unit> Deserialize<'de> for Vector<F, U> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct VectorVisitor<F, U>(PhantomData<(F, U)>);

        impl<'de, F: ReferenceFrame, U: Unit> Visitor<'de> for VectorVisitor<F, U> {
            type Value = Vector<F, U>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a Vector with an xyz field")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut xyz: Option<XYZ<Quantity<U>>> = None;

                while let Some(key) = map.next_key::<&str>()? {
                    match key {
                        "xyz" => {
                            if xyz.is_some() {
                                return Err(de::Error::duplicate_field("xyz"));
                            }
                            xyz = Some(map.next_value()?);
                        }
                        _ => {
                            let _ = map.next_value::<de::IgnoredAny>()?;
                        }
                    }
                }

                let xyz = xyz.ok_or_else(|| de::Error::missing_field("xyz"))?;
                Ok(Vector {
                    xyz,
                    _frame: PhantomData,
                })
            }
        }

        deserializer.deserialize_struct("Vector", &["xyz"], VectorVisitor(PhantomData))
    }
}
