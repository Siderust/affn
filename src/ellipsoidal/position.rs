//! # Ellipsoidal Position
//!
//! This module defines the core ellipsoidal [`Position`] type
//! (center + frame + height-above-ellipsoid).
//!
//! ## Mathematical Model
//!
//! An ellipsoidal position represents a point via:
//! - **lon (λ)**: Geodetic longitude, positive **eastward** — range `[-180°, +180°)`
//! - **lat (φ)**: Geodetic latitude, positive **northward** — range `[-90°, +90°]`
//! - **height (h)**: Height above the reference ellipsoid
//!
//! ## Type Parameters
//!
//! - `C`: Reference center (defines the origin)
//! - `F`: Reference frame (carries the ellipsoid via [`HasEllipsoid`](crate::ellipsoid::HasEllipsoid))
//! - `U`: Length unit for the height (defaults to [`Meter`])
//!
//! ## Conversion to Cartesian
//!
//! Call [`to_cartesian()`](Position::to_cartesian) to get a
//! [`cartesian::Position<C, F, U>`](crate::cartesian::Position).  This method
//! is only available when `F: HasEllipsoid`, ensuring that the correct ellipsoid
//! constants are used at compile time.
//!
//! ## Example
//!
//! ```rust
//! use affn::ellipsoidal::Position;
//! use affn::frames::ReferenceFrame;
//! use affn::centers::ReferenceCenter;
//! use qtty::units::*; use qtty::{Quantity, M, KM, DEG, RAD, SEC}; use qtty::angular::{Degrees, Radians}; use qtty::length::{Meters, Kilometers};
//!
//! #[derive(Debug, Copy, Clone)]
//! struct Geocentric;
//! impl ReferenceCenter for Geocentric {
//!     type Params = ();
//!     fn center_name() -> &'static str { "Geocentric" }
//! }
//!
//! // Any frame with HasEllipsoid works; for a standalone example we use
//! // the built-in ECEF frame (requires the `astro` feature).
//! # #[cfg(feature = "astro")]
//! let pos = Position::<Geocentric, affn::frames::ECEF, Meter>::new(
//!     -17.89 * DEG,
//!     28.76 * DEG,
//!     2200.0 * M,
//! );
//! ```

use crate::centers::ReferenceCenter;
use crate::ellipsoid::{Ellipsoid, HasEllipsoid};
use crate::frames::ReferenceFrame;
use qtty::angular::Degrees;
use qtty::length::LengthUnit;
use qtty::length::Meters;
use qtty::units::{Meter, Radian};
use qtty::Quantity;

use std::marker::PhantomData;

// Serde implementations in separate module
#[cfg(feature = "serde")]
#[path = "position_serde.rs"]
mod position_serde;

/// Error returned by [`Position::try_from_cartesian`] when the Bowring
/// iteration fails to converge below the latitude residual threshold
/// (`1e-14` rad) within the iteration cap.
#[derive(Debug, Clone, PartialEq)]
pub struct GeodeticConvergenceError {
    /// Number of Bowring iterations performed before giving up.
    pub iterations: u32,
    /// Absolute latitude residual `(lat_new - lat_prev).abs()` (in radians)
    /// observed at the last iteration.
    pub last_residual: f64,
}

impl std::fmt::Display for GeodeticConvergenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "geodetic Bowring iteration failed to converge after {} iterations \
             (last latitude residual: {:e} rad)",
            self.iterations, self.last_residual
        )
    }
}

impl std::error::Error for GeodeticConvergenceError {}

/// An ellipsoidal **position** (center + frame + height above ellipsoid).
///
/// This is the fundamental ellipsoidal (geodetic) coordinate type,
/// analogous to [`spherical::Position`](crate::spherical::Position) for
/// spherical coordinates.
///
/// # Type Parameters
///
/// - `C`: The reference center (e.g., `Geocentric`)
/// - `F`: The reference frame; determines the ellipsoid via
///   [`HasEllipsoid`](crate::ellipsoid::HasEllipsoid)
/// - `U`: The length unit for the height (defaults to [`Meter`])
///
/// # Field conventions
///
/// | Field    | Meaning                                    |
/// |----------|--------------------------------------------|
/// | `lon`    | Geodetic longitude, positive **eastward**  |
/// | `lat`    | Geodetic latitude, positive **northward**  |
/// | `height` | Height above the reference ellipsoid        |
///
/// # Correctness note
///
/// Do **not** convert this value using spherical-to-Cartesian formulas.
/// Always use the ellipsoid-aware
/// [`to_cartesian`](Position::to_cartesian) method.
#[derive(Debug, Clone, Copy)]
pub struct Position<C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit = Meter> {
    /// Geodetic longitude (positive eastward), in degrees.
    pub lon: Degrees,
    /// Geodetic latitude (positive northward), in degrees.
    pub lat: Degrees,
    /// Height above the reference ellipsoid.
    pub height: Quantity<U>,

    center_params: C::Params,
    _frame: PhantomData<F>,
}

// =============================================================================
// PartialEq (conditional on C::Params: PartialEq)
// =============================================================================

impl<C, F, U> PartialEq for Position<C, F, U>
where
    C: ReferenceCenter,
    C::Params: PartialEq,
    F: ReferenceFrame,
    U: LengthUnit,
{
    fn eq(&self, other: &Self) -> bool {
        self.lon == other.lon
            && self.lat == other.lat
            && self.height == other.height
            && self.center_params == other.center_params
    }
}

// =============================================================================
// Constructors with explicit center parameters
// =============================================================================

impl<C, F, U> Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    /// Const-fn constructor with explicit center parameters.
    ///
    /// Longitude and latitude are stored **as-is** (no normalisation).
    /// Use [`new_with_params`](Self::new_with_params) if you want automatic
    /// normalisation.
    pub const fn new_raw_with_params(
        center_params: C::Params,
        lon: Degrees,
        lat: Degrees,
        height: Quantity<U>,
    ) -> Self {
        Self {
            lon,
            lat,
            height,
            center_params,
            _frame: PhantomData,
        }
    }

    /// Constructor with explicit center parameters and lon/lat normalisation.
    ///
    /// Longitude is normalised to `[-180°, +180°)` and latitude to `[-90°, +90°]`
    /// (pole-crossing is reflected into longitude).
    pub fn new_with_params(
        center_params: C::Params,
        lon: Degrees,
        lat: Degrees,
        height: Quantity<U>,
    ) -> Self {
        let (lon_n, lat_n) = super::normalize_lon_lat(lon.value(), lat.value());
        Self::new_raw_with_params(
            center_params,
            Degrees::new(lon_n),
            Degrees::new(lat_n),
            height,
        )
    }

    /// Returns a reference to the center parameters.
    #[inline]
    pub fn center_params(&self) -> &C::Params {
        &self.center_params
    }
}

// =============================================================================
// Convenience constructors for centers with Params = ()
// =============================================================================

impl<C, F, U> Position<C, F, U>
where
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    /// Const-fn constructor (no normalisation) for centers with `Params = ()`.
    pub const fn new_raw(lon: Degrees, lat: Degrees, height: Quantity<U>) -> Self {
        Self::new_raw_with_params((), lon, lat, height)
    }

    /// Normalising constructor for centers with `Params = ()`.
    pub fn new(lon: Degrees, lat: Degrees, height: Quantity<U>) -> Self {
        Self::new_with_params((), lon, lat, height)
    }

    /// Normalising constructor (infallible `Result` wrapper kept for API compat).
    pub fn try_new(
        lon: Degrees,
        lat: Degrees,
        height: Quantity<U>,
    ) -> Result<Self, core::convert::Infallible> {
        Ok(Self::new(lon, lat, height))
    }

    /// The geodetic origin: (0°E, 0°N, 0 height-units).
    pub const ORIGIN: Self = Self::new_raw(
        Degrees::new(0.0),
        Degrees::new(0.0),
        Quantity::<U>::new(0.0),
    );
}

// =============================================================================
// Ellipsoid-aware conversions (trait-gated on HasEllipsoid)
// =============================================================================

impl<C, F, U> Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame + HasEllipsoid,
    U: LengthUnit,
{
    /// Converts to a Cartesian ECEF position using the ellipsoid of frame `F`.
    ///
    /// The ellipsoid constants are obtained from `F::Ellipsoid` at compile time.
    ///
    /// # Type Parameter
    ///
    /// - `TargetU`: length unit for the output `Position`
    ///
    /// # Example
    ///
    /// ```rust
    /// use affn::ellipsoidal::Position;
    /// use affn::centers::ReferenceCenter;
    /// use qtty::units::*; use qtty::{Quantity, M, KM, DEG, RAD, SEC}; use qtty::angular::{Degrees, Radians}; use qtty::length::{Meters, Kilometers};
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct Geocentric;
    /// impl ReferenceCenter for Geocentric {
    ///     type Params = ();
    ///     fn center_name() -> &'static str { "Geocentric" }
    /// }
    ///
    /// # #[cfg(feature = "astro")]
    /// {
    ///     let obs = Position::<Geocentric, affn::frames::ECEF, Meter>::new(
    ///         -17.89 * DEG, 28.76 * DEG, 2200.0 * M,
    ///     );
    ///     let cart: affn::cartesian::Position<Geocentric, affn::frames::ECEF, Meter> =
    ///         obs.to_cartesian();
    ///     // X ≈ 5 390 km, Y ≈ −1 730 km, Z ≈ 3 050 km (approx. La Palma)
    /// }
    /// ```
    pub fn to_cartesian<TargetU: LengthUnit>(&self) -> crate::cartesian::Position<C, F, TargetU>
    where
        C::Params: Clone,
    {
        let a = <F::Ellipsoid as Ellipsoid>::A;
        let e2 = <F::Ellipsoid>::e2();

        let lat_rad = self.lat.to::<Radian>();
        let lon_rad = self.lon.to::<Radian>();
        let h: Meters = self.height.to::<Meter>();

        let (sin_lat, cos_lat) = lat_rad.sin_cos();
        let (sin_lon, cos_lon) = lon_rad.sin_cos();

        // Radius of curvature in the prime vertical (metres)
        let n = Meters::new(a / (1.0 - e2 * sin_lat * sin_lat).sqrt());

        // Geocentric Cartesian coordinates (metres)
        let x_m = (n + h) * cos_lat * cos_lon;
        let y_m = (n + h) * cos_lat * sin_lon;
        let z_m = (n * (1.0 - e2) + h) * sin_lat;

        crate::cartesian::Position::<C, F, TargetU>::new_with_params(
            self.center_params.clone(),
            x_m.to::<TargetU>(),
            y_m.to::<TargetU>(),
            z_m.to::<TargetU>(),
        )
    }

    /// Constructs an ellipsoidal position from a Cartesian ECEF position using
    /// the ellipsoid of frame `F`.
    ///
    /// Uses the iterative Bowring algorithm (typically 2–3 iterations for
    /// sub-millimetre accuracy).
    ///
    /// This is an **infallible best-effort wrapper**; prefer
    /// [`try_from_cartesian`](Self::try_from_cartesian) when convergence
    /// guarantees matter. If the Bowring iteration does not converge within
    /// the iteration cap, this method returns the last computed iterate
    /// without signalling the failure.
    ///
    /// # Type Parameter
    ///
    /// - `SourceU`: length unit of the input `Position`
    ///
    /// # Example
    ///
    /// ```rust
    /// use affn::ellipsoidal::Position;
    /// use affn::centers::ReferenceCenter;
    /// use qtty::units::*; use qtty::{Quantity, M, KM, DEG, RAD, SEC}; use qtty::angular::{Degrees, Radians}; use qtty::length::{Meters, Kilometers};
    ///
    /// #[derive(Debug, Copy, Clone)]
    /// struct Geocentric;
    /// impl ReferenceCenter for Geocentric {
    ///     type Params = ();
    ///     fn center_name() -> &'static str { "Geocentric" }
    /// }
    ///
    /// # #[cfg(feature = "astro")]
    /// {
    ///     let obs = Position::<Geocentric, affn::frames::ECEF, Meter>::new(
    ///         -17.89 * DEG, 28.76 * DEG, 2200.0 * M,
    ///     );
    ///     let cart = obs.to_cartesian::<Meter>();
    ///     let back = Position::<Geocentric, affn::frames::ECEF, Meter>::from_cartesian(&cart);
    ///     assert!((back.lat.value() - obs.lat.value()).abs() < 1e-10);
    /// }
    /// ```
    pub fn from_cartesian<SourceU: LengthUnit>(
        pos: &crate::cartesian::Position<C, F, SourceU>,
    ) -> Self
    where
        C::Params: Clone,
    {
        Self::try_from_cartesian(pos).unwrap_or_else(|_| Self::from_cartesian_best_effort(pos))
    }

    /// Fallible counterpart of [`from_cartesian`](Self::from_cartesian).
    ///
    /// Runs the same Bowring iteration, but returns
    /// [`Err(GeodeticConvergenceError)`](GeodeticConvergenceError) when the
    /// latitude residual `(lat_new - lat_prev).abs()` still exceeds the
    /// convergence threshold (`1e-14` rad) after the iteration cap.
    ///
    /// # Type Parameter
    ///
    /// - `SourceU`: length unit of the input `Position`
    pub fn try_from_cartesian<SourceU: LengthUnit>(
        pos: &crate::cartesian::Position<C, F, SourceU>,
    ) -> Result<Self, GeodeticConvergenceError>
    where
        C::Params: Clone,
    {
        const MAX_ITERATIONS: u32 = 5;
        const CONVERGENCE_THRESHOLD: f64 = 1e-14;

        let a = <F::Ellipsoid as Ellipsoid>::A;
        let e2 = <F::Ellipsoid>::e2();
        let b = <F::Ellipsoid>::b();

        let x = pos.x().to::<Meter>().value();
        let y = pos.y().to::<Meter>().value();
        let z = pos.z().to::<Meter>().value();

        let lon_rad = y.atan2(x);
        let p = (x * x + y * y).sqrt();

        let ep2 = (a * a - b * b) / (b * b);
        let theta = (z * a).atan2(p * b);
        let sin_theta = theta.sin();
        let cos_theta = theta.cos();

        let mut lat = (z + ep2 * b * sin_theta * sin_theta * sin_theta)
            .atan2(p - e2 * a * cos_theta * cos_theta * cos_theta);

        let mut last_residual = f64::INFINITY;
        let mut iterations: u32 = 0;
        for _ in 0..MAX_ITERATIONS {
            iterations += 1;
            let sin_lat = lat.sin();
            let new_lat = {
                let n = a / (1.0 - e2 * sin_lat * sin_lat).sqrt();
                (z + e2 * n * sin_lat).atan2(p)
            };
            last_residual = (new_lat - lat).abs();
            lat = new_lat;
            if last_residual < CONVERGENCE_THRESHOLD {
                break;
            }
        }

        if last_residual >= CONVERGENCE_THRESHOLD {
            return Err(GeodeticConvergenceError {
                iterations,
                last_residual,
            });
        }

        let sin_lat = lat.sin();
        let cos_lat = lat.cos();
        let n = a / (1.0 - e2 * sin_lat * sin_lat).sqrt();
        let h = if cos_lat.abs() > 1e-10 {
            p / cos_lat - n
        } else {
            z / sin_lat - n * (1.0 - e2)
        };

        Ok(Self::new_with_params(
            pos.center_params().clone(),
            Degrees::new(lon_rad.to_degrees()),
            Degrees::new(lat.to_degrees()),
            Meters::new(h).to::<U>(),
        ))
    }

    /// Best-effort fallback used by [`from_cartesian`](Self::from_cartesian)
    /// when the Bowring iteration does not converge: returns the last iterate
    /// without signalling the failure (preserves pre-existing behaviour).
    fn from_cartesian_best_effort<SourceU: LengthUnit>(
        pos: &crate::cartesian::Position<C, F, SourceU>,
    ) -> Self
    where
        C::Params: Clone,
    {
        let a = <F::Ellipsoid as Ellipsoid>::A;
        let e2 = <F::Ellipsoid>::e2();
        let b = <F::Ellipsoid>::b();

        let x = pos.x().to::<Meter>().value();
        let y = pos.y().to::<Meter>().value();
        let z = pos.z().to::<Meter>().value();

        let lon_rad = y.atan2(x);
        let p = (x * x + y * y).sqrt();

        let ep2 = (a * a - b * b) / (b * b);
        let theta = (z * a).atan2(p * b);
        let sin_theta = theta.sin();
        let cos_theta = theta.cos();

        let mut lat = (z + ep2 * b * sin_theta * sin_theta * sin_theta)
            .atan2(p - e2 * a * cos_theta * cos_theta * cos_theta);

        for _ in 0..5 {
            let sin_lat = lat.sin();
            let n = a / (1.0 - e2 * sin_lat * sin_lat).sqrt();
            lat = (z + e2 * n * sin_lat).atan2(p);
        }

        let sin_lat = lat.sin();
        let cos_lat = lat.cos();
        let n = a / (1.0 - e2 * sin_lat * sin_lat).sqrt();
        let h = if cos_lat.abs() > 1e-10 {
            p / cos_lat - n
        } else {
            z / sin_lat - n * (1.0 - e2)
        };

        Self::new_with_params(
            pos.center_params().clone(),
            Degrees::new(lon_rad.to_degrees()),
            Degrees::new(lat.to_degrees()),
            Meters::new(h).to::<U>(),
        )
    }
}

// =============================================================================
// Default (Params = (), U = Meter)
// =============================================================================

impl<C, F> Default for Position<C, F, Meter>
where
    C: ReferenceCenter<Params = ()>,
    F: ReferenceFrame,
{
    /// Returns the geodetic origin: (0°E, 0°N, 0 m).
    fn default() -> Self {
        Self::new_raw(
            Degrees::new(0.0),
            Degrees::new(0.0),
            Quantity::<Meter>::new(0.0),
        )
    }
}

// =============================================================================
// Display
// =============================================================================

impl_quantity_fmt_triplet! {
    impl[C, F, U] for Position<C, F, U>
    where {
        C: ReferenceCenter,
        F: ReferenceFrame,
        U: LengthUnit,
    },
    fmt_each: { Quantity<U>, },
    |this, f, FmtOne| {
        write!(
            f,
            "Center: {}, Frame: {}, lon: ",
            C::center_name(),
            F::frame_name()
        )?;
        FmtOne::fmt(&this.lon, f)?;
        write!(f, ", lat: ")?;
        FmtOne::fmt(&this.lat, f)?;
        write!(f, ", h: ")?;
        FmtOne::fmt(&this.height, f)
    }
}

// =============================================================================
// Unit tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};

    #[allow(unused_imports)]
    use qtty::angular::{Degrees, Radians};
    #[allow(unused_imports)]
    use qtty::length::{Kilometers, Meters};
    use qtty::units::{Kilometer, Meter};
    use qtty::{DEG, M};
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestFrame;

    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct TestCenter;

    #[derive(Clone, Debug, Default, PartialEq)]
    struct TestParams {
        id: i32,
    }

    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    #[center(params = TestParams)]
    struct ParamCenter;

    #[test]
    fn new_stores_values() {
        let p = Position::<TestCenter, TestFrame, Meter>::new(10.0 * DEG, 20.0 * DEG, 100.0 * M);
        assert_eq!(p.lon, 10.0 * DEG);
        assert_eq!(p.lat, 20.0 * DEG);
        assert_eq!(p.height, 100.0 * M);
    }

    #[test]
    fn new_normalises_angles() {
        let p = Position::<TestCenter, TestFrame, Meter>::new(540.0 * DEG, 100.0 * DEG, 1.0 * M);
        assert_eq!(p.lon, 0.0 * DEG);
        assert_eq!(p.lat, 80.0 * DEG);
    }

    #[test]
    fn new_raw_does_not_normalise() {
        let p =
            Position::<TestCenter, TestFrame, Meter>::new_raw(540.0 * DEG, 100.0 * DEG, 1.0 * M);
        assert_eq!(p.lon, 540.0 * DEG);
        assert_eq!(p.lat, 100.0 * DEG);
    }

    #[test]
    fn default_is_origin() {
        let d = Position::<TestCenter, TestFrame, Meter>::default();
        assert_eq!(d.lon, 0.0 * DEG);
        assert_eq!(d.lat, 0.0 * DEG);
        assert_eq!(d.height, 0.0 * M);
    }

    #[test]
    fn equality_and_inequality() {
        let a = Position::<TestCenter, TestFrame, Meter>::new(1.0 * DEG, 2.0 * DEG, 3.0 * M);
        let b = Position::<TestCenter, TestFrame, Meter>::new(1.0 * DEG, 2.0 * DEG, 3.0 * M);
        let c = Position::<TestCenter, TestFrame, Meter>::new(1.0 * DEG, 2.0 * DEG, 4.0 * M);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn generic_height_unit() {
        let p = Position::<TestCenter, TestFrame, Kilometer>::new(
            0.0 * DEG,
            0.0 * DEG,
            Kilometers::new(10.0),
        );
        assert_eq!(p.height, Kilometers::new(10.0));
    }

    #[test]
    fn with_center_params() {
        let params = TestParams { id: 42 };
        let p = Position::<ParamCenter, TestFrame, Meter>::new_raw_with_params(
            params.clone(),
            5.0 * DEG,
            10.0 * DEG,
            2.0 * M,
        );
        assert_eq!(p.center_params(), &params);
    }

    #[test]
    fn try_new_is_infallible() {
        let p = Position::<TestCenter, TestFrame, Meter>::try_new(0.0 * DEG, 271.0 * DEG, 0.0 * M)
            .unwrap();
        assert_eq!(p.lat, -89.0 * DEG);
    }

    #[test]
    fn display() {
        let p = Position::<TestCenter, TestFrame, Meter>::new(10.0 * DEG, 20.0 * DEG, 100.0 * M);
        let s = p.to_string();
        assert!(s.contains("TestCenter"));
        assert!(s.contains("TestFrame"));

        let s_prec = format!("{:.2}", p);
        let expected_h_prec = format!("{:.2}", p.height);
        assert!(s_prec.contains(&format!("h: {expected_h_prec}")));

        let s_exp = format!("{:.3e}", p);
        let expected_lon_exp = format!("{:.3e}", p.lon);
        assert!(s_exp.contains(&format!("lon: {expected_lon_exp}")));
    }

    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestEllipsoidFrame;

    impl crate::ellipsoid::HasEllipsoid for TestEllipsoidFrame {
        type Ellipsoid = crate::ellipsoid::Wgs84;
    }

    #[test]
    fn try_from_cartesian_round_trip_converges() {
        let original = Position::<TestCenter, TestEllipsoidFrame, Meter>::new(
            -17.89 * DEG,
            28.76 * DEG,
            2200.0 * M,
        );
        let cart = original.to_cartesian::<Meter>();
        let back = Position::<TestCenter, TestEllipsoidFrame, Meter>::try_from_cartesian(&cart)
            .expect("Bowring iteration should converge for a well-defined point");

        // Sub-microarcsecond agreement on lon/lat (1 µas ≈ 2.78e-10 deg).
        let max_angle_err_deg = 1.0e-10;
        assert!(
            (back.lon.value() - original.lon.value()).abs() < max_angle_err_deg,
            "longitude residual {} exceeds tolerance",
            (back.lon.value() - original.lon.value()).abs()
        );
        assert!(
            (back.lat.value() - original.lat.value()).abs() < max_angle_err_deg,
            "latitude residual {} exceeds tolerance",
            (back.lat.value() - original.lat.value()).abs()
        );
        // Height should round-trip to sub-millimetre.
        assert!(
            (back.height.value() - original.height.value()).abs() < 1.0e-6,
            "height residual {} m exceeds tolerance",
            (back.height.value() - original.height.value()).abs()
        );
    }

    #[test]
    fn geodetic_convergence_error_display_mentions_residual() {
        let err = GeodeticConvergenceError {
            iterations: 5,
            last_residual: 1.5e-10,
        };
        let msg = format!("{err}");
        assert!(msg.contains("5"));
        assert!(msg.contains("1.5e-10") || msg.contains("1.5e-10"));
    }
}
