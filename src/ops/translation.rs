//! Translation vector operator.

use crate::cartesian::xyz::XYZ;
use qtty::units::Meter;
use qtty::{Quantity, Unit};
use std::marker::PhantomData;

/// A unit-typed translation vector in 3D space.
///
/// This is a pure mathematical operator representing a displacement.
/// The type parameter `U` carries the unit of the displacement components,
/// so that mixing translations built from different units is a compile-time
/// error when applied to typed coordinates.
///
/// # Usage
///
/// Translations apply only to positions (affine points), not to directions
/// or vectors (which are translation-invariant).
///
/// # Unit Safety
///
/// `Translation3<AU>` applied to a `Position<C, F, AU>` shifts it by the
/// stored AU values. Applying it to a `Position<C, F, KM>` is a compile-time
/// error because the unit parameters do not match.
///
/// Use [`to_unit`](Self::to_unit) to convert a translation from one unit to another
/// (performing the appropriate scale factor).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Translation3<U: Unit = Meter> {
    /// The translation vector components, in unit `U`.
    pub v: [f64; 3],
    _unit: PhantomData<U>,
}

impl<U: Unit> Translation3<U> {
    /// Zero translation (no displacement).
    pub const ZERO: Self = Self {
        v: [0.0, 0.0, 0.0],
        _unit: PhantomData,
    };

    /// Creates a new translation from raw component values in unit `U`.
    #[inline]
    #[must_use]
    pub const fn new(x: f64, y: f64, z: f64) -> Self {
        Self {
            v: [x, y, z],
            _unit: PhantomData,
        }
    }

    /// Creates a translation from a raw array in unit `U`.
    #[inline]
    #[must_use]
    pub const fn from_array(v: [f64; 3]) -> Self {
        Self {
            v,
            _unit: PhantomData,
        }
    }

    /// Creates a translation from an `XYZ<f64>` in unit `U`.
    #[inline]
    #[must_use]
    pub fn from_xyz(xyz: XYZ<f64>) -> Self {
        Self::new(xyz.x(), xyz.y(), xyz.z())
    }

    /// Returns the inverse translation.
    #[inline]
    #[must_use]
    pub fn inverse(&self) -> Self {
        Self::new(-self.v[0], -self.v[1], -self.v[2])
    }

    /// Composes two translations: `self + other`.
    #[inline]
    #[must_use]
    pub fn compose(&self, other: &Self) -> Self {
        Self::new(
            self.v[0] + other.v[0],
            self.v[1] + other.v[1],
            self.v[2] + other.v[2],
        )
    }

    /// Applies this translation to a raw `[f64; 3]` array.
    ///
    /// The caller is responsible for ensuring the array values are in the
    /// same unit as the translation.
    #[inline]
    pub fn apply_array(&self, v: [f64; 3]) -> [f64; 3] {
        [v[0] + self.v[0], v[1] + self.v[1], v[2] + self.v[2]]
    }

    /// Applies this translation to an `XYZ<f64>`.
    #[inline]
    pub fn apply_xyz(&self, xyz: XYZ<f64>) -> XYZ<f64> {
        let [x, y, z] = self.apply_array([xyz.x(), xyz.y(), xyz.z()]);
        XYZ::new(x, y, z)
    }

    /// Returns the translation as an array.
    #[inline]
    pub const fn as_array(&self) -> &[f64; 3] {
        &self.v
    }

    /// Returns the translation components as typed [`Quantity`] values.
    ///
    /// The output unit must have the same dimension as `U`; magnitudes are
    /// converted with `qtty` rather than re-wrapped.
    #[inline]
    pub fn as_quantities<U2: Unit<Dim = U::Dim>>(&self) -> [Quantity<U2>; 3] {
        [
            Quantity::<U>::new(self.v[0]).to::<U2>(),
            Quantity::<U>::new(self.v[1]).to::<U2>(),
            Quantity::<U>::new(self.v[2]).to::<U2>(),
        ]
    }

    /// Returns the translation as an `XYZ<f64>`.
    #[inline]
    pub fn as_xyz(&self) -> XYZ<f64> {
        XYZ::new(self.v[0], self.v[1], self.v[2])
    }

    /// Converts this translation to a different unit of the same dimension.
    ///
    /// The stored magnitudes are scaled by the appropriate conversion factor.
    #[inline]
    #[must_use]
    pub fn to_unit<U2: Unit<Dim = U::Dim>>(&self) -> Translation3<U2> {
        let [x, y, z] = self.as_quantities::<U2>();
        Translation3::new(x.value(), y.value(), z.value())
    }
}

impl Translation3 {
    /// Creates a translation from typed [`Quantity`] values.
    ///
    /// The raw `f64` magnitudes are extracted and stored. The returned
    /// translation is typed to the same unit as the input quantities.
    ///
    /// # Example
    /// ```
    /// use affn::ops::Translation3;
    /// use qtty::units::*; use qtty::{Quantity, AU};
    /// use qtty::length::AstronomicalUnits;
    ///
    /// let t = Translation3::from_quantities([1.0 * AU, 0.5 * AU, -0.3 * AU]);
    /// // t is Translation3<AstronomicalUnit>
    /// assert!((t.v[0] - 1.0).abs() < 1e-12);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_quantities<U: Unit>(v: [Quantity<U>; 3]) -> Translation3<U> {
        Translation3::<U>::new(v[0].value(), v[1].value(), v[2].value())
    }
}

impl<U: Unit> Default for Translation3<U> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<U: Unit> std::ops::Add for Translation3<U> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        self.compose(&rhs)
    }
}

impl<U: Unit> std::ops::Neg for Translation3<U> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.inverse()
    }
}

/// Applies a translation to a raw `[f64; 3]` point: `p + t`.
///
/// The caller is responsible for ensuring the array values are in the
/// same unit as the translation.
impl<U: Unit> std::ops::Mul<[f64; 3]> for Translation3<U> {
    type Output = [f64; 3];

    #[inline]
    fn mul(self, rhs: [f64; 3]) -> [f64; 3] {
        self.apply_array(rhs)
    }
}

// Mul<[Quantity<U>; 3]>, Mul<XYZ<Quantity<U>>>, and Mul<Position<C,F,U>>
// are implemented directly in the parent module (ops/mod.rs).

#[cfg(test)]
mod tests {
    use super::*;

    const EPSILON: f64 = 1e-12;

    fn assert_array_eq(a: [f64; 3], b: [f64; 3], msg: &str) {
        assert!(
            (a[0] - b[0]).abs() < EPSILON
                && (a[1] - b[1]).abs() < EPSILON
                && (a[2] - b[2]).abs() < EPSILON,
            "{}: {:?} != {:?}",
            msg,
            a,
            b
        );
    }

    use qtty::units::{AstronomicalUnit, Kilometer, Meter};

    #[test]
    fn test_translation_zero() {
        let t = Translation3::<Meter>::ZERO;
        let v = [1.0, 2.0, 3.0];
        assert_array_eq(
            t.apply_array(v),
            v,
            "Zero translation should not change point",
        );
    }

    #[test]
    fn test_translation_apply() {
        let t = Translation3::<Meter>::new(1.0, 2.0, 3.0);
        let p = [0.0, 0.0, 0.0];
        assert_array_eq(
            t.apply_array(p),
            [1.0, 2.0, 3.0],
            "Translation should offset point",
        );
    }

    #[test]
    fn test_translation_inverse() {
        let t = Translation3::<Meter>::new(1.0, 2.0, 3.0);
        let t_inv = t.inverse();
        let p = [0.0, 0.0, 0.0];
        let result = t_inv.apply_array(t.apply_array(p));
        assert_array_eq(result, p, "T * T^-1 should return to origin");
    }

    #[test]
    fn test_translation_compose() {
        let t1 = Translation3::<Meter>::new(1.0, 0.0, 0.0);
        let t2 = Translation3::<Meter>::new(0.0, 1.0, 0.0);
        let composed = t1.compose(&t2);
        let p = [0.0, 0.0, 0.0];
        assert_array_eq(
            composed.apply_array(p),
            [1.0, 1.0, 0.0],
            "Composed translation",
        );
    }

    #[test]
    fn test_translation_helpers_and_ops() {
        let t = Translation3::<Meter>::from_array([1.0, 2.0, 3.0]);
        assert_eq!(t.as_array(), &[1.0, 2.0, 3.0]);

        let applied = t.apply_xyz(crate::cartesian::xyz::XYZ::new(0.0, 0.0, 0.0));
        assert_array_eq(
            [applied.x(), applied.y(), applied.z()],
            [1.0, 2.0, 3.0],
            "apply_xyz",
        );

        let sum = t + Translation3::<Meter>::new(1.0, 0.0, 0.0);
        assert_eq!(sum.as_array(), &[2.0, 2.0, 3.0]);
        let neg = -t;
        assert_eq!(neg.as_array(), &[-1.0, -2.0, -3.0]);

        let default = Translation3::<Meter>::default();
        assert_eq!(default, Translation3::<Meter>::ZERO);
        let as_xyz = t.as_xyz();
        assert_array_eq(
            [as_xyz.x(), as_xyz.y(), as_xyz.z()],
            [1.0, 2.0, 3.0],
            "as_xyz",
        );
    }

    #[test]
    fn test_translation_mul_f64_array() {
        let t = Translation3::<Meter>::new(1.0, 2.0, 3.0);
        let result = t * [0.0, 0.0, 0.0];
        assert_array_eq(result, [1.0, 2.0, 3.0], "Translation * [f64; 3]");
    }

    #[test]
    fn test_translation_mul_quantity_array() {
        use qtty::Quantity;
        let t = Translation3::<Meter>::new(1.0, 2.0, 3.0);
        let v = [
            Quantity::<Meter>::new(10.0),
            Quantity::<Meter>::new(20.0),
            Quantity::<Meter>::new(30.0),
        ];
        let result = t * v;
        assert!((result[0].value() - 11.0).abs() < EPSILON);
        assert!((result[1].value() - 22.0).abs() < EPSILON);
        assert!((result[2].value() - 33.0).abs() < EPSILON);
    }

    #[test]
    fn test_translation_from_quantities() {
        use qtty::Quantity;
        let q = [
            Quantity::<AstronomicalUnit>::new(1.0),
            Quantity::<AstronomicalUnit>::new(0.5),
            Quantity::<AstronomicalUnit>::new(-0.3),
        ];
        let t = Translation3::from_quantities(q);
        // t is now Translation3<AstronomicalUnit>
        assert!((t.v[0] - 1.0).abs() < EPSILON);
        assert!((t.v[1] - 0.5).abs() < EPSILON);
        assert!((t.v[2] - (-0.3)).abs() < EPSILON);
    }

    #[test]
    fn test_translation_as_quantities() {
        use qtty::Quantity;
        let t = Translation3::<Kilometer>::new(100.0, 200.0, 300.0);
        let q: [Quantity<Kilometer>; 3] = t.as_quantities();
        assert!((q[0].value() - 100.0).abs() < EPSILON);
        assert!((q[1].value() - 200.0).abs() < EPSILON);
        assert!((q[2].value() - 300.0).abs() < EPSILON);
    }

    #[test]
    fn test_translation_to_unit() {
        // 1 AU ≈ 1.495978707e11 m
        let t_au = Translation3::from_quantities([1.0 * qtty::AU, 0.0 * qtty::AU, 0.0 * qtty::AU]);
        let t_km: Translation3<Kilometer> = t_au.to_unit();
        // 1 AU = 149_597_870.7 km
        assert!(
            (t_km.v[0] - 149_597_870.7).abs() < 1.0,
            "AU→km conversion: got {}",
            t_km.v[0]
        );
    }

    #[test]
    fn test_translation_from_as_quantities_roundtrip() {
        use qtty::Quantity;
        let original = [
            Quantity::<Meter>::new(1.5),
            Quantity::<Meter>::new(-2.3),
            Quantity::<Meter>::new(4.7),
        ];
        let t = Translation3::from_quantities(original);
        let back: [Quantity<Meter>; 3] = t.as_quantities();
        assert!((back[0].value() - original[0].value()).abs() < EPSILON);
        assert!((back[1].value() - original[1].value()).abs() < EPSILON);
        assert!((back[2].value() - original[2].value()).abs() < EPSILON);
    }
}
