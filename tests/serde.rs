//! Serde serialization/deserialization tests for affn types.
//!
//! These tests verify that all core coordinate types can be round-tripped
//! through JSON serialization without losing data.

#![cfg(feature = "serde")]

use affn::cartesian::{Direction as CartesianDirection, Displacement, Position, Vector};
use affn::centers::ReferenceCenter;
use affn::conic::{ConicOrientation, OrientedConic, PeriapsisParam, SemiMajorAxisParam};
#[cfg(feature = "astro")]
use affn::frames::EclipticMeanJ2000;
use affn::frames::{ReferenceFrame, SphericalNaming};
use affn::spherical::{Direction as SphericalDirection, Position as SphericalPosition};
use qtty::units::{AstronomicalUnit, Kilometer, Meter, Second};
use qtty::{Per, AU, DEG, KM, M};
use serde::{Deserialize, Serialize};

// =============================================================================
// Test Frame and Center Definitions
// =============================================================================

#[derive(Debug, Copy, Clone, PartialEq)]
struct TestFrame;

impl ReferenceFrame for TestFrame {
    fn frame_name() -> &'static str {
        "TestFrame"
    }
}

// Use default naming (polar/azimuth) for test frame
impl SphericalNaming for TestFrame {
    fn polar_name() -> &'static str {
        "polar"
    }
    fn azimuth_name() -> &'static str {
        "azimuth"
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
struct TestCenter;

impl ReferenceCenter for TestCenter {
    type Params = ();
    fn center_name() -> &'static str {
        "TestCenter"
    }
}

/// A center with runtime parameters for testing serde bounds.
#[derive(Debug, Copy, Clone, PartialEq)]
struct ParameterizedCenter;

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
struct CenterParams {
    x: f64,
    y: f64,
    z: f64,
}

impl ReferenceCenter for ParameterizedCenter {
    type Params = CenterParams;
    fn center_name() -> &'static str {
        "ParameterizedCenter"
    }
}

// =============================================================================
// Cartesian Vector Tests
// =============================================================================

#[test]
fn test_vector_serde_roundtrip() {
    let vec = Vector::<TestFrame, Meter>::new(1.0, 2.0, 3.0);

    let json = serde_json::to_string(&vec).expect("serialize Vector");
    let deserialized: Vector<TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize Vector");

    assert_eq!(vec.x(), deserialized.x());
    assert_eq!(vec.y(), deserialized.y());
    assert_eq!(vec.z(), deserialized.z());
}

#[test]
fn test_displacement_serde_roundtrip() {
    let disp = Displacement::<TestFrame, Kilometer>::new(100.0, 200.0, 300.0);

    let json = serde_json::to_string(&disp).expect("serialize Displacement");
    let deserialized: Displacement<TestFrame, Kilometer> =
        serde_json::from_str(&json).expect("deserialize Displacement");

    assert_eq!(disp.x(), deserialized.x());
    assert_eq!(disp.y(), deserialized.y());
    assert_eq!(disp.z(), deserialized.z());
}

#[test]
fn test_vector_with_compound_unit_serde_roundtrip() {
    type MeterPerSecond = Per<Meter, Second>;
    let vel = Vector::<TestFrame, MeterPerSecond>::new(10.0, 20.0, 30.0);

    let json = serde_json::to_string(&vel).expect("serialize velocity Vector");
    let deserialized: Vector<TestFrame, MeterPerSecond> =
        serde_json::from_str(&json).expect("deserialize velocity Vector");

    assert_eq!(vel.x(), deserialized.x());
    assert_eq!(vel.y(), deserialized.y());
    assert_eq!(vel.z(), deserialized.z());
}

// =============================================================================
// Cartesian Direction Tests
// =============================================================================

#[test]
fn test_cartesian_direction_serde_roundtrip() {
    let dir = CartesianDirection::<TestFrame>::new(1.0, 2.0, 2.0);

    let json = serde_json::to_string(&dir).expect("serialize CartesianDirection");
    let deserialized: CartesianDirection<TestFrame> =
        serde_json::from_str(&json).expect("deserialize CartesianDirection");

    // Directions are normalized, so compare with tolerance
    assert!((dir.x() - deserialized.x()).abs() < 1e-12);
    assert!((dir.y() - deserialized.y()).abs() < 1e-12);
    assert!((dir.z() - deserialized.z()).abs() < 1e-12);
}

#[test]
fn test_cartesian_direction_unit_axes_serde() {
    let x_axis = CartesianDirection::<TestFrame>::new(1.0, 0.0, 0.0);
    let y_axis = CartesianDirection::<TestFrame>::new(0.0, 1.0, 0.0);
    let z_axis = CartesianDirection::<TestFrame>::new(0.0, 0.0, 1.0);

    for dir in [x_axis, y_axis, z_axis] {
        let json = serde_json::to_string(&dir).expect("serialize axis");
        let deserialized: CartesianDirection<TestFrame> =
            serde_json::from_str(&json).expect("deserialize axis");

        assert!((dir.x() - deserialized.x()).abs() < 1e-12);
        assert!((dir.y() - deserialized.y()).abs() < 1e-12);
        assert!((dir.z() - deserialized.z()).abs() < 1e-12);
    }
}

// =============================================================================
// Cartesian Position Tests
// =============================================================================

#[test]
fn test_cartesian_position_serde_roundtrip() {
    let pos = Position::<TestCenter, TestFrame, AstronomicalUnit>::new(1.0, 2.0, 3.0);

    let json = serde_json::to_string(&pos).expect("serialize Position");
    let deserialized: Position<TestCenter, TestFrame, AstronomicalUnit> =
        serde_json::from_str(&json).expect("deserialize Position");

    assert_eq!(pos.x(), deserialized.x());
    assert_eq!(pos.y(), deserialized.y());
    assert_eq!(pos.z(), deserialized.z());
}

#[test]
fn test_cartesian_position_with_params_serde_roundtrip() {
    let params = CenterParams {
        x: 10.0,
        y: 20.0,
        z: 30.0,
    };
    let pos = Position::<ParameterizedCenter, TestFrame, Kilometer>::new_with_params(
        params.clone(),
        100.0,
        200.0,
        300.0,
    );

    let json = serde_json::to_string(&pos).expect("serialize Position with params");
    let deserialized: Position<ParameterizedCenter, TestFrame, Kilometer> =
        serde_json::from_str(&json).expect("deserialize Position with params");

    assert_eq!(pos.x(), deserialized.x());
    assert_eq!(pos.y(), deserialized.y());
    assert_eq!(pos.z(), deserialized.z());
    assert_eq!(pos.center_params(), deserialized.center_params());
}

#[test]
fn test_cartesian_position_origin_serde() {
    let origin = Position::<TestCenter, TestFrame, Meter>::new(0.0, 0.0, 0.0);

    let json = serde_json::to_string(&origin).expect("serialize origin");
    let deserialized: Position<TestCenter, TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize origin");

    assert_eq!(origin.x().value(), deserialized.x().value());
    assert_eq!(origin.y().value(), deserialized.y().value());
    assert_eq!(origin.z().value(), deserialized.z().value());
}

// =============================================================================
// Spherical Direction Tests
// =============================================================================

#[test]
fn test_spherical_direction_serde_roundtrip() {
    let dir = SphericalDirection::<TestFrame>::new_unchecked(45.0 * DEG, 90.0 * DEG);

    let json = serde_json::to_string(&dir).expect("serialize SphericalDirection");
    let deserialized: SphericalDirection<TestFrame> =
        serde_json::from_str(&json).expect("deserialize SphericalDirection");

    assert!((dir.polar.value() - deserialized.polar.value()).abs() < 1e-12);
    assert!((dir.azimuth.value() - deserialized.azimuth.value()).abs() < 1e-12);
}

#[test]
fn test_spherical_direction_poles_serde() {
    let north_pole = SphericalDirection::<TestFrame>::new_unchecked(90.0 * DEG, 0.0 * DEG);
    let south_pole = SphericalDirection::<TestFrame>::new_unchecked(-90.0 * DEG, 0.0 * DEG);

    for dir in [north_pole, south_pole] {
        let json = serde_json::to_string(&dir).expect("serialize pole");
        let deserialized: SphericalDirection<TestFrame> =
            serde_json::from_str(&json).expect("deserialize pole");

        assert!((dir.polar.value() - deserialized.polar.value()).abs() < 1e-12);
        assert!((dir.azimuth.value() - deserialized.azimuth.value()).abs() < 1e-12);
    }
}

#[test]
fn test_spherical_direction_equator_serde() {
    // Test points on the equator at various azimuths
    for azimuth in [0.0, 90.0, 180.0, 270.0, 359.9] {
        let dir = SphericalDirection::<TestFrame>::new_unchecked(0.0 * DEG, azimuth * DEG);

        let json = serde_json::to_string(&dir).expect("serialize equator point");
        let deserialized: SphericalDirection<TestFrame> =
            serde_json::from_str(&json).expect("deserialize equator point");

        assert!((dir.polar.value() - deserialized.polar.value()).abs() < 1e-12);
        assert!((dir.azimuth.value() - deserialized.azimuth.value()).abs() < 1e-12);
    }
}

// =============================================================================
// Spherical Position Tests
// =============================================================================

#[test]
fn test_spherical_position_serde_roundtrip() {
    let pos = SphericalPosition::<TestCenter, TestFrame, Kilometer>::new_unchecked(
        45.0 * DEG,
        90.0 * DEG,
        1000.0 * KM,
    );

    let json = serde_json::to_string(&pos).expect("serialize SphericalPosition");
    let deserialized: SphericalPosition<TestCenter, TestFrame, Kilometer> =
        serde_json::from_str(&json).expect("deserialize SphericalPosition");

    assert!((pos.polar.value() - deserialized.polar.value()).abs() < 1e-12);
    assert!((pos.azimuth.value() - deserialized.azimuth.value()).abs() < 1e-12);
    assert_eq!(pos.distance, deserialized.distance);
}

#[test]
fn test_spherical_position_with_params_serde_roundtrip() {
    let params = CenterParams {
        x: 1.0,
        y: 2.0,
        z: 3.0,
    };
    let pos = SphericalPosition::<ParameterizedCenter, TestFrame, AstronomicalUnit>::new_unchecked_with_params(
        params.clone(),
        30.0 * DEG,
        60.0 * DEG,
        1.5 * AU,
    );

    let json = serde_json::to_string(&pos).expect("serialize SphericalPosition with params");
    let deserialized: SphericalPosition<ParameterizedCenter, TestFrame, AstronomicalUnit> =
        serde_json::from_str(&json).expect("deserialize SphericalPosition with params");

    assert!((pos.polar.value() - deserialized.polar.value()).abs() < 1e-12);
    assert!((pos.azimuth.value() - deserialized.azimuth.value()).abs() < 1e-12);
    assert_eq!(pos.distance, deserialized.distance);
    assert_eq!(pos.center_params(), deserialized.center_params());
}

// =============================================================================
// JSON Structure Tests
// =============================================================================

#[test]
fn test_vector_json_structure() {
    let vec = Vector::<TestFrame, Meter>::new(1.0, 2.0, 3.0);
    let json = serde_json::to_string_pretty(&vec).expect("serialize Vector");

    // Verify JSON is valid and can be parsed
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert!(value.is_object());
}

#[test]
fn test_position_json_structure() {
    let pos = Position::<TestCenter, TestFrame, Meter>::new(1.0, 2.0, 3.0);
    let json = serde_json::to_string_pretty(&pos).expect("serialize Position");

    // Verify JSON is valid and can be parsed
    let value: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert!(value.is_object());
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_vector_with_special_values_serde() {
    // Test with very small values
    let small = Vector::<TestFrame, Meter>::new(1e-300, 1e-300, 1e-300);
    let json = serde_json::to_string(&small).expect("serialize small vector");
    let deserialized: Vector<TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize small vector");
    assert_eq!(small.x(), deserialized.x());

    // Test with very large values
    let large = Vector::<TestFrame, Meter>::new(1e300, 1e300, 1e300);
    let json = serde_json::to_string(&large).expect("serialize large vector");
    let deserialized: Vector<TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize large vector");
    assert_eq!(large.x(), deserialized.x());
}

#[test]
fn test_zero_vector_serde() {
    let zero = Vector::<TestFrame, Meter>::new(0.0, 0.0, 0.0);

    let json = serde_json::to_string(&zero).expect("serialize zero vector");
    let deserialized: Vector<TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize zero vector");

    assert_eq!(zero.x().value(), deserialized.x().value());
    assert_eq!(zero.y().value(), deserialized.y().value());
    assert_eq!(zero.z().value(), deserialized.z().value());
}

#[test]
fn test_negative_values_serde() {
    let neg = Vector::<TestFrame, Meter>::new(-1.0, -2.0, -3.0);

    let json = serde_json::to_string(&neg).expect("serialize negative vector");
    let deserialized: Vector<TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize negative vector");

    assert_eq!(neg.x(), deserialized.x());
    assert_eq!(neg.y(), deserialized.y());
    assert_eq!(neg.z(), deserialized.z());
}

// =============================================================================
// Conic Geometry Tests
// =============================================================================

#[test]
fn test_periapsis_param_serde_roundtrip() {
    let conic = PeriapsisParam::try_new(1.25 * AU, 0.42).unwrap();

    let json = serde_json::to_string(&conic).expect("serialize PeriapsisParam");
    let deserialized: PeriapsisParam<AstronomicalUnit> =
        serde_json::from_str(&json).expect("deserialize PeriapsisParam");

    assert_eq!(conic, deserialized);
}

#[test]
fn test_semi_major_axis_param_serde_roundtrip() {
    let conic = SemiMajorAxisParam::try_new(2.5 * KM, 0.2).unwrap();

    let json = serde_json::to_string(&conic).expect("serialize SemiMajorAxisParam");
    let deserialized: SemiMajorAxisParam<Kilometer> =
        serde_json::from_str(&json).expect("deserialize SemiMajorAxisParam");

    assert_eq!(conic, deserialized);
}

#[test]
#[cfg(feature = "astro")]
fn test_oriented_conic_serde_roundtrip() {
    let orientation =
        ConicOrientation::<EclipticMeanJ2000>::try_new(12.0 * DEG, 34.0 * DEG, 56.0 * DEG).unwrap();
    let periapsis: OrientedConic<PeriapsisParam<AstronomicalUnit>, EclipticMeanJ2000> =
        OrientedConic::new(PeriapsisParam::try_new(0.5 * AU, 1.4).unwrap(), orientation);
    let semi_major: OrientedConic<SemiMajorAxisParam<Meter>, EclipticMeanJ2000> =
        OrientedConic::new(
            SemiMajorAxisParam::try_new(5.0 * M, 0.1).unwrap(),
            orientation,
        );

    let periapsis_json =
        serde_json::to_string(&periapsis).expect("serialize OrientedConic<PeriapsisParam, _>");
    let periapsis_deserialized: OrientedConic<PeriapsisParam<AstronomicalUnit>, EclipticMeanJ2000> =
        serde_json::from_str(&periapsis_json).expect("deserialize OrientedConic<PeriapsisParam, _>");
    assert_eq!(periapsis, periapsis_deserialized);

    let semi_major_json =
        serde_json::to_string(&semi_major).expect("serialize OrientedConic<SemiMajorAxisParam, _>");
    let semi_major_deserialized: OrientedConic<SemiMajorAxisParam<Meter>, EclipticMeanJ2000> =
        serde_json::from_str(&semi_major_json)
            .expect("deserialize OrientedConic<SemiMajorAxisParam, _>");
    assert_eq!(semi_major, semi_major_deserialized);
}

// =============================================================================
// Ellipsoidal Position Serde Tests
// =============================================================================

#[test]
fn test_ellipsoidal_position_serde_roundtrip() {
    use affn::ellipsoidal::Position as EllipsoidalPosition;
    use qtty::angular::Degrees;
    use qtty::units::Meter;

    let pos = EllipsoidalPosition::<TestCenter, TestFrame, Meter>::new(
        Degrees::new(10.5),
        Degrees::new(48.2),
        qtty::Quantity::<Meter>::new(350.0),
    );

    let json = serde_json::to_string(&pos).expect("serialize ellipsoidal Position");
    let deserialized: EllipsoidalPosition<TestCenter, TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize ellipsoidal Position");

    assert_eq!(pos.lon, deserialized.lon);
    assert_eq!(pos.lat, deserialized.lat);
    assert_eq!(pos.height, deserialized.height);
}

#[test]
fn test_ellipsoidal_position_serde_with_center_params() {
    use affn::ellipsoidal::Position as EllipsoidalPosition;
    use qtty::angular::Degrees;
    use qtty::units::Meter;

    let params = CenterParams {
        x: 1.0,
        y: 2.0,
        z: 3.0,
    };
    let pos = EllipsoidalPosition::<ParameterizedCenter, TestFrame, Meter>::new_with_params(
        params.clone(),
        Degrees::new(-74.0),
        Degrees::new(40.7),
        qtty::Quantity::<Meter>::new(10.0),
    );

    let json = serde_json::to_string(&pos).expect("serialize ellipsoidal Position with params");
    assert!(json.contains("center_params"));
    let deserialized: EllipsoidalPosition<ParameterizedCenter, TestFrame, Meter> =
        serde_json::from_str(&json).expect("deserialize ellipsoidal Position with params");

    assert_eq!(pos.center_params(), deserialized.center_params());
    assert_eq!(pos.lon, deserialized.lon);
    assert_eq!(pos.lat, deserialized.lat);
    assert_eq!(pos.height, deserialized.height);
}

#[test]
fn test_ellipsoidal_position_serde_missing_field_error() {
    use affn::ellipsoidal::Position as EllipsoidalPosition;
    use qtty::units::Meter;

    let bad_json = r#"{"lon_deg": 10.0, "lat_deg": 20.0}"#;
    let result =
        serde_json::from_str::<EllipsoidalPosition<TestCenter, TestFrame, Meter>>(bad_json);
    assert!(result.is_err());
}

#[test]
fn test_ellipsoidal_position_serde_duplicate_field_error() {
    use affn::ellipsoidal::Position as EllipsoidalPosition;
    use qtty::units::Meter;

    let bad_json = r#"{"lon_deg": 10.0, "lon_deg": 11.0, "lat_deg": 20.0, "height": 0.0}"#;
    let result =
        serde_json::from_str::<EllipsoidalPosition<TestCenter, TestFrame, Meter>>(bad_json);
    assert!(result.is_err());
}

#[test]
fn test_ellipsoidal_position_serde_unknown_field_ignored() {
    use affn::ellipsoidal::Position as EllipsoidalPosition;
    use qtty::units::Meter;

    let json_with_extra =
        r#"{"lon_deg": 5.0, "lat_deg": 10.0, "height": 100.0, "unknown": "ignored"}"#;
    let result =
        serde_json::from_str::<EllipsoidalPosition<TestCenter, TestFrame, Meter>>(json_with_extra);
    assert!(result.is_ok());
}

// =============================================================================
// Conic serde error path tests
// =============================================================================

#[test]
fn test_periapsis_param_serde_rejects_invalid() {
    // eccentricity = -1 is invalid; deserialization should fail
    let bad_json = r#"{"periapsis_distance": 1000.0, "eccentricity": -1.0}"#;
    let result = serde_json::from_str::<PeriapsisParam<Meter>>(bad_json);
    assert!(result.is_err());
}

#[test]
fn test_semi_major_axis_param_serde_rejects_parabolic() {
    let bad_json = r#"{"semi_major_axis": 1000.0, "eccentricity": 1.0}"#;
    let result = serde_json::from_str::<SemiMajorAxisParam<Meter>>(bad_json);
    assert!(result.is_err());
}

#[test]
#[cfg(feature = "astro")]
fn test_conic_orientation_serde_roundtrip() {
    let ori =
        ConicOrientation::<EclipticMeanJ2000>::try_new(30.0 * DEG, 60.0 * DEG, 90.0 * DEG).unwrap();
    let json = serde_json::to_string(&ori).expect("serialize ConicOrientation");
    let deserialized: ConicOrientation<EclipticMeanJ2000> =
        serde_json::from_str(&json).expect("deserialize ConicOrientation");
    assert_eq!(ori.inclination(), deserialized.inclination());
    assert_eq!(
        ori.longitude_of_ascending_node(),
        deserialized.longitude_of_ascending_node()
    );
    assert_eq!(
        ori.argument_of_periapsis(),
        deserialized.argument_of_periapsis()
    );
}

#[test]
#[cfg(feature = "astro")]
fn test_conic_orientation_serde_rejects_non_finite() {
    let bad_json = r#"{"inclination": 0.0, "longitude_of_ascending_node": 0.0, "argument_of_periapsis": "inf"}"#;
    let result = serde_json::from_str::<ConicOrientation<EclipticMeanJ2000>>(bad_json);
    assert!(result.is_err());
}
