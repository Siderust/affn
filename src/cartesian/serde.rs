//! Serde implementations for Cartesian Vector and Direction types.

use super::{Direction, Vector};
use crate::cartesian::xyz::XYZ;
use crate::frames::ReferenceFrame;
use crate::serde_utils::{collect_field, skip_unknown, take_required};
use qtty::{Quantity, Unit};
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::marker::PhantomData;

// =============================================================================
// Vector<F, U>
// =============================================================================

impl<F: ReferenceFrame, U: Unit> Serialize for Vector<F, U> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("Vector", 1)?;
        state.serialize_field("xyz", &self.xyz)?;
        state.end()
    }
}

impl<'de, F: ReferenceFrame, U: Unit> Deserialize<'de> for Vector<F, U> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct VectorVisitor<F, U>(PhantomData<(F, U)>);

        impl<'de, F: ReferenceFrame, U: Unit> Visitor<'de> for VectorVisitor<F, U> {
            type Value = Vector<F, U>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a Vector with an xyz field")
            }

            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                let mut xyz: Option<XYZ<Quantity<U>>> = None;
                while let Some(key) = map.next_key::<&str>()? {
                    match key {
                        "xyz" => collect_field(&mut xyz, "xyz", &mut map)?,
                        _ => skip_unknown(&mut map)?,
                    }
                }
                Ok(Vector::from_xyz(take_required(xyz, "xyz")?))
            }
        }

        deserializer.deserialize_struct("Vector", &["xyz"], VectorVisitor(PhantomData))
    }
}

// =============================================================================
// Direction<F>
// =============================================================================

impl<F: ReferenceFrame> Serialize for Direction<F> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("Direction", 1)?;
        state.serialize_field("xyz", &self.xyz)?;
        state.end()
    }
}

impl<'de, F: ReferenceFrame> Deserialize<'de> for Direction<F> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct DirectionVisitor<F>(PhantomData<F>);

        impl<'de, F: ReferenceFrame> Visitor<'de> for DirectionVisitor<F> {
            type Value = Direction<F>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a Direction with an xyz field")
            }

            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
                // Direction<F> is always XYZ<f64> — directions are dimensionless
                // unit vectors, so there is no length unit U, unlike Vector<F, U>.
                let mut xyz: Option<XYZ<f64>> = None;
                while let Some(key) = map.next_key::<&str>()? {
                    match key {
                        "xyz" => collect_field(&mut xyz, "xyz", &mut map)?,
                        _ => skip_unknown(&mut map)?,
                    }
                }
                Ok(Direction::from_xyz_unchecked(take_required(xyz, "xyz")?))
            }
        }

        deserializer.deserialize_struct("Direction", &["xyz"], DirectionVisitor(PhantomData))
    }
}
