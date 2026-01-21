//! Serde serialization/deserialization tests for affn types.
//!
//! These tests verify that all core coordinate types can be round-tripped
//! through JSON serialization without losing data.

#![cfg(feature = "serde")]

use affn::cartesian::{Direction as CartesianDirection, Displacement, Position, Vector};
use affn::centers::ReferenceCenter;
use affn::frames::{ReferenceFrame, SphericalNaming};
use affn::spherical::{Direction as SphericalDirection, Position as SphericalPosition};
use qtty::*;
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
    let dir = SphericalDirection::<TestFrame>::new(45.0 * DEG, 90.0 * DEG);

    let json = serde_json::to_string(&dir).expect("serialize SphericalDirection");
    let deserialized: SphericalDirection<TestFrame> =
        serde_json::from_str(&json).expect("deserialize SphericalDirection");

    assert!((dir.polar.value() - deserialized.polar.value()).abs() < 1e-12);
    assert!((dir.azimuth.value() - deserialized.azimuth.value()).abs() < 1e-12);
}

#[test]
fn test_spherical_direction_poles_serde() {
    let north_pole = SphericalDirection::<TestFrame>::new(90.0 * DEG, 0.0 * DEG);
    let south_pole = SphericalDirection::<TestFrame>::new(-90.0 * DEG, 0.0 * DEG);

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
        let dir = SphericalDirection::<TestFrame>::new(0.0 * DEG, azimuth * DEG);

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
    let pos = SphericalPosition::<TestCenter, TestFrame, Kilometer>::new_raw(
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
    let pos = SphericalPosition::<ParameterizedCenter, TestFrame, AstronomicalUnit>::new_raw_with_params(
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
