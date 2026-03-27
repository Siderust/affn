//! Frame-tagged orientation values for conic sections.

use std::marker::PhantomData;

use qtty::Degrees;

use crate::frames::ReferenceFrame;

use super::ConicValidationError;

/// Orientation of a conic in 3D space within a specific reference frame.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ConicOrientation<F: ReferenceFrame> {
    inclination: Degrees,
    longitude_of_ascending_node: Degrees,
    argument_of_periapsis: Degrees,
    _frame: PhantomData<F>,
}

impl<F: ReferenceFrame> ConicOrientation<F> {
    /// Constructs a validated orientation in frame `F`.
    ///
    /// All three angles must be finite. The values are stored exactly as given;
    /// this constructor does not normalize or wrap them.
    pub fn try_new(
        inclination: Degrees,
        longitude_of_ascending_node: Degrees,
        argument_of_periapsis: Degrees,
    ) -> Result<Self, ConicValidationError> {
        if !inclination.value().is_finite()
            || !longitude_of_ascending_node.value().is_finite()
            || !argument_of_periapsis.value().is_finite()
        {
            return Err(ConicValidationError::InvalidOrientation);
        }
        Ok(Self {
            inclination,
            longitude_of_ascending_node,
            argument_of_periapsis,
            _frame: PhantomData,
        })
    }

    /// Constructs an orientation without validation.
    ///
    /// Intended for trusted or compile-time data where finiteness has already
    /// been established by the caller.
    pub const fn new(
        inclination: Degrees,
        longitude_of_ascending_node: Degrees,
        argument_of_periapsis: Degrees,
    ) -> Self {
        Self {
            inclination,
            longitude_of_ascending_node,
            argument_of_periapsis,
            _frame: PhantomData,
        }
    }

    /// Returns the stored inclination of the conic plane.
    #[inline]
    pub const fn inclination(&self) -> Degrees {
        self.inclination
    }

    /// Returns the stored longitude of the ascending node.
    #[inline]
    pub const fn longitude_of_ascending_node(&self) -> Degrees {
        self.longitude_of_ascending_node
    }

    /// Returns the stored argument of periapsis.
    #[inline]
    pub const fn argument_of_periapsis(&self) -> Degrees {
        self.argument_of_periapsis
    }
}

#[cfg(feature = "serde")]
mod orientation_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    struct ConicOrientationProxy {
        inclination: Degrees,
        longitude_of_ascending_node: Degrees,
        argument_of_periapsis: Degrees,
    }

    impl<F: ReferenceFrame> Serialize for ConicOrientation<F> {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            ConicOrientationProxy {
                inclination: self.inclination,
                longitude_of_ascending_node: self.longitude_of_ascending_node,
                argument_of_periapsis: self.argument_of_periapsis,
            }
            .serialize(s)
        }
    }

    impl<'de, F: ReferenceFrame> Deserialize<'de> for ConicOrientation<F> {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            let proxy = ConicOrientationProxy::deserialize(d)?;
            ConicOrientation::try_new(
                proxy.inclination,
                proxy.longitude_of_ascending_node,
                proxy.argument_of_periapsis,
            )
            .map_err(serde::de::Error::custom)
        }
    }
}
