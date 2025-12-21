//! Integration tests for the affn-derive macros.

use affn::prelude::*;

// =============================================================================
// ReferenceFrame derive tests
// =============================================================================

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct SimpleFrame;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
#[frame(name = "Custom Frame Name")]
struct CustomNameFrame;

#[test]
fn test_derive_frame_simple() {
    assert_eq!(SimpleFrame::frame_name(), "SimpleFrame");
}

#[test]
fn test_derive_frame_custom_name() {
    assert_eq!(CustomNameFrame::frame_name(), "Custom Frame Name");
}

#[test]
fn test_derive_frame_zero_sized() {
    assert_eq!(std::mem::size_of::<SimpleFrame>(), 0);
    assert_eq!(std::mem::size_of::<CustomNameFrame>(), 0);
}

// =============================================================================
// ReferenceCenter derive tests
// =============================================================================

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct SimpleCenter;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
#[center(name = "Custom Center Name")]
struct CustomNameCenter;

#[derive(Clone, Debug, Default, PartialEq)]
struct MyParams {
    value: f64,
}

#[derive(Debug, Copy, Clone, ReferenceCenter)]
#[center(params = MyParams)]
struct ParameterizedCenter;

#[allow(dead_code)]
#[derive(Debug, Copy, Clone, ReferenceCenter)]
#[center(affine = false)]
struct NonAffineCenter;

#[test]
fn test_derive_center_simple() {
    assert_eq!(SimpleCenter::center_name(), "SimpleCenter");
    assert_eq!(
        std::mem::size_of::<<SimpleCenter as affn::centers::ReferenceCenter>::Params>(),
        0
    );
}

#[test]
fn test_derive_center_custom_name() {
    assert_eq!(CustomNameCenter::center_name(), "Custom Center Name");
}

#[test]
fn test_derive_center_parameterized() {
    assert_eq!(ParameterizedCenter::center_name(), "ParameterizedCenter");
    // Verify the Params type is correctly set
    let _params: <ParameterizedCenter as affn::centers::ReferenceCenter>::Params =
        MyParams { value: 42.0 };
}

#[test]
fn test_derive_center_zero_sized() {
    assert_eq!(std::mem::size_of::<SimpleCenter>(), 0);
    assert_eq!(std::mem::size_of::<CustomNameCenter>(), 0);
}

#[test]
fn test_derive_center_affine() {
    // Simple centers should implement AffineCenter
    fn assert_affine<T: affn::centers::AffineCenter>() {}
    assert_affine::<SimpleCenter>();
    assert_affine::<CustomNameCenter>();

    // NonAffineCenter should NOT implement AffineCenter
    // This won't compile: assert_affine::<NonAffineCenter>();
}

// =============================================================================
// Usage with Position types
// =============================================================================

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct TestFrame;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct TestCenter;

#[test]
fn test_derive_with_position() {
    use qtty::Kilometer;

    let pos = Position::<TestCenter, TestFrame, Kilometer>::new(1.0, 2.0, 3.0);
    assert_eq!(pos.x().value(), 1.0);
    assert_eq!(pos.y().value(), 2.0);
    assert_eq!(pos.z().value(), 3.0);
}

// =============================================================================
// Multiple attributes test
// =============================================================================

#[derive(Debug, Copy, Clone, ReferenceCenter)]
#[center(name = "Multi Attr Center", params = MyParams)]
struct MultiAttrCenter;

#[test]
fn test_derive_center_multiple_attrs() {
    assert_eq!(MultiAttrCenter::center_name(), "Multi Attr Center");
    let _params: <MultiAttrCenter as affn::centers::ReferenceCenter>::Params =
        MyParams { value: 99.0 };
}
