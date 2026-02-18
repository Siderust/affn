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
//! use qtty::*;
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
use qtty::{Degrees, LengthUnit, Meter, Meters, Quantity, Radian};

use std::marker::PhantomData;

// Serde implementations in separate module
#[cfg(feature = "serde")]
#[path = "position_serde.rs"]
mod position_serde;

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
    /// use qtty::*;
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
    /// # Type Parameter
    ///
    /// - `SourceU`: length unit of the input `Position`
    ///
    /// # Example
    ///
    /// ```rust
    /// use affn::ellipsoidal::Position;
    /// use affn::centers::ReferenceCenter;
    /// use qtty::*;
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
        let a = <F::Ellipsoid as Ellipsoid>::A;
        let e2 = <F::Ellipsoid>::e2();
        let b = <F::Ellipsoid>::b();

        // Convert input position to metres
        let x = pos.x().to::<Meter>().value();
        let y = pos.y().to::<Meter>().value();
        let z = pos.z().to::<Meter>().value();

        // Longitude is straightforward
        let lon_rad = y.atan2(x);

        // Bowring iterative algorithm for latitude and height
        let p = (x * x + y * y).sqrt();

        // Initial approximation (Bowring 1985)
        let ep2 = (a * a - b * b) / (b * b); // second eccentricity squared
        let theta = (z * a).atan2(p * b);
        let sin_theta = theta.sin();
        let cos_theta = theta.cos();

        let mut lat = (z + ep2 * b * sin_theta * sin_theta * sin_theta)
            .atan2(p - e2 * a * cos_theta * cos_theta * cos_theta);

        // Iterate (typically 2-3 iterations for sub-mm convergence)
        for _ in 0..5 {
            let sin_lat = lat.sin();
            let cos_lat = lat.cos();
            let n = a / (1.0 - e2 * sin_lat * sin_lat).sqrt();
            let h = if cos_lat.abs() > 1e-10 {
                p / cos_lat - n
            } else {
                z / sin_lat - n * (1.0 - e2)
            };

            let new_lat = (z + e2 * n * sin_lat).atan2(p);
            if (new_lat - lat).abs() < 1e-14 {
                // Converged — compute final height and return
                let lon_deg = lon_rad.to_degrees();
                let lat_deg = new_lat.to_degrees();
                return Self::new_with_params(
                    pos.center_params().clone(),
                    Degrees::new(lon_deg),
                    Degrees::new(lat_deg),
                    Meters::new(h).to::<U>(),
                );
            }
            lat = new_lat;
        }

        // Final result after max iterations
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

impl<C, F, U> std::fmt::Display for Position<C, F, U>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
    Quantity<U>: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Center: {}, Frame: {}, lon: {:.6}, lat: {:.6}, h: {}",
            C::center_name(),
            F::frame_name(),
            self.lon,
            self.lat,
            self.height,
        )
    }
}

// =============================================================================
// Unit tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};
    use qtty::*;

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
    }
}
