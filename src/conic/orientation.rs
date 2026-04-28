//! Frame-tagged orientation values for conic sections.

use std::marker::PhantomData;

use qtty::angular::Degrees;

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
    /// Constructs a validated orientation in frame `F`, **canonicalizing**
    /// out-of-range angles into their conventional intervals.
    ///
    /// All three angles must be finite; non-finite inputs return
    /// [`ConicValidationError::InvalidOrientation`].
    ///
    /// Canonicalization policy:
    ///
    /// * `longitude_of_ascending_node` and `argument_of_periapsis` are wrapped
    ///   into `[0°, 360°)` via `rem_euclid`.
    /// * `inclination` is folded into `[0°, 180°]`. The raw value is first
    ///   wrapped into `[0°, 360°)`; if the result exceeds `180°`, it is
    ///   reflected as `i' = 360° - i` and the longitude of the ascending node
    ///   is rotated by `180°` to keep the orbital plane and periapsis
    ///   direction geometrically equivalent.
    ///
    /// Use [`Self::try_new_strict`] if you instead want out-of-range inputs
    /// to be rejected rather than silently canonicalized.
    pub fn try_new(
        inclination: Degrees,
        longitude_of_ascending_node: Degrees,
        argument_of_periapsis: Degrees,
    ) -> Result<Self, ConicValidationError> {
        if !inclination.is_finite()
            || !longitude_of_ascending_node.is_finite()
            || !argument_of_periapsis.is_finite()
        {
            return Err(ConicValidationError::InvalidOrientation);
        }

        let mut lan_deg = longitude_of_ascending_node.rem_euclid(360.0);
        let aop_deg = argument_of_periapsis.rem_euclid(360.0);

        let mut i_deg = inclination.rem_euclid(360.0);
        if i_deg > Degrees::new(180.0) {
            i_deg = Degrees::new(360.0) - i_deg;
            lan_deg = (lan_deg + Degrees::new(180.0)).rem_euclid(360.0);
        }

        Ok(Self {
            inclination: i_deg,
            longitude_of_ascending_node: lan_deg,
            argument_of_periapsis: aop_deg,
            _frame: PhantomData,
        })
    }

    /// Constructs a validated orientation in frame `F` **without**
    /// canonicalizing the inputs.
    ///
    /// All three angles must be finite; non-finite inputs return
    /// [`ConicValidationError::InvalidOrientation`].
    ///
    /// In addition, each angle must already lie within its conventional
    /// interval:
    ///
    /// * `inclination` ∈ `[0°, 180°]`
    /// * `longitude_of_ascending_node` ∈ `[0°, 360°)`
    /// * `argument_of_periapsis` ∈ `[0°, 360°)`
    ///
    /// Any value outside its range produces
    /// [`ConicValidationError::OutOfRange`] identifying the offending field.
    /// Use [`Self::try_new`] if you prefer silent canonicalization.
    pub fn try_new_strict(
        inclination: Degrees,
        longitude_of_ascending_node: Degrees,
        argument_of_periapsis: Degrees,
    ) -> Result<Self, ConicValidationError> {
        if !inclination.is_finite()
            || !longitude_of_ascending_node.is_finite()
            || !argument_of_periapsis.is_finite()
        {
            return Err(ConicValidationError::InvalidOrientation);
        }

        if !(Degrees::new(0.0)..=Degrees::new(180.0)).contains(&inclination) {
            return Err(ConicValidationError::OutOfRange {
                field: "inclination",
                value: inclination.value(),
            });
        }

        if !(Degrees::new(0.0)..Degrees::new(360.0)).contains(&longitude_of_ascending_node) {
            return Err(ConicValidationError::OutOfRange {
                field: "longitude_of_ascending_node",
                value: longitude_of_ascending_node.value(),
            });
        }

        if !(Degrees::new(0.0)..Degrees::new(360.0)).contains(&argument_of_periapsis) {
            return Err(ConicValidationError::OutOfRange {
                field: "argument_of_periapsis",
                value: argument_of_periapsis.value(),
            });
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
