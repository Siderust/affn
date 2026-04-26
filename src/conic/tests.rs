use super::*;
#[allow(unused_imports)]
use qtty::angular::{Degrees, Radians};
#[allow(unused_imports)]
use qtty::length::{Kilometers, Meters};
use qtty::units::Meter;
use qtty::{DEG, M};
#[derive(Debug, Copy, Clone, PartialEq)]
struct TestFrame;
impl crate::frames::ReferenceFrame for TestFrame {
    fn frame_name() -> &'static str {
        "TestFrame"
    }
}

fn orientation() -> ConicOrientation<TestFrame> {
    ConicOrientation::try_new(10.0 * DEG, 20.0 * DEG, 30.0 * DEG).unwrap()
}

#[test]
fn periapsis_try_new_rejects_zero_distance() {
    assert_eq!(
        PeriapsisParam::try_new(0.0 * M, 0.5),
        Err(ConicValidationError::InvalidPeriapsisDistance)
    );
}

#[test]
fn periapsis_try_new_rejects_negative_eccentricity() {
    assert_eq!(
        PeriapsisParam::try_new(1.0 * M, -0.1),
        Err(ConicValidationError::InvalidEccentricity)
    );
}

#[test]
fn sma_try_new_rejects_zero_axis() {
    assert_eq!(
        SemiMajorAxisParam::try_new(0.0 * M, 0.5),
        Err(ConicValidationError::InvalidSemiMajorAxis)
    );
}

#[test]
fn sma_try_new_rejects_parabolic() {
    assert_eq!(
        SemiMajorAxisParam::try_new(1.0 * M, 1.0),
        Err(ConicValidationError::ParabolicSemiMajorAxis)
    );
}

#[test]
fn orientation_try_new_rejects_nan() {
    assert_eq!(
        ConicOrientation::<TestFrame>::try_new(
            Degrees::new(f64::NAN),
            Degrees::new(0.0),
            Degrees::new(0.0)
        ),
        Err(ConicValidationError::InvalidOrientation)
    );
}

#[test]
fn orientation_try_new_rejects_infinity() {
    assert_eq!(
        ConicOrientation::<TestFrame>::try_new(
            Degrees::new(0.0),
            Degrees::new(f64::INFINITY),
            Degrees::new(0.0)
        ),
        Err(ConicValidationError::InvalidOrientation)
    );
}

#[test]
fn periapsis_kind_elliptic() {
    let s = PeriapsisParam::try_new(1.0 * M, 0.5).unwrap();
    assert_eq!(s.kind(), ConicKind::Elliptic);
}

#[test]
fn periapsis_kind_parabolic() {
    let s = PeriapsisParam::try_new(1.0 * M, 1.0).unwrap();
    assert_eq!(s.kind(), ConicKind::Parabolic);
}

#[test]
fn periapsis_kind_hyperbolic() {
    let s = PeriapsisParam::try_new(1.0 * M, 1.5).unwrap();
    assert_eq!(s.kind(), ConicKind::Hyperbolic);
}

#[test]
fn classify_periapsis_elliptic() {
    let s = PeriapsisParam::try_new(1.0 * M, 0.5).unwrap();
    assert!(matches!(
        s.classify(),
        ClassifiedPeriapsisParam::Elliptic(_)
    ));
}

#[test]
fn classify_periapsis_parabolic() {
    let s = PeriapsisParam::try_new(1.0 * M, 1.0).unwrap();
    assert!(matches!(
        s.classify(),
        ClassifiedPeriapsisParam::Parabolic(_)
    ));
}

#[test]
fn classify_periapsis_hyperbolic() {
    let s = PeriapsisParam::try_new(1.0 * M, 1.5).unwrap();
    assert!(matches!(
        s.classify(),
        ClassifiedPeriapsisParam::Hyperbolic(_)
    ));
}

#[test]
fn classify_sma_elliptic() {
    let s = SemiMajorAxisParam::try_new(1.0 * M, 0.5).unwrap();
    assert!(matches!(
        s.classify(),
        ClassifiedSemiMajorAxisParam::Elliptic(_)
    ));
}

#[test]
fn classify_sma_hyperbolic() {
    let s = SemiMajorAxisParam::try_new(1.0 * M, 1.5).unwrap();
    assert!(matches!(
        s.classify(),
        ClassifiedSemiMajorAxisParam::Hyperbolic(_)
    ));
}

#[test]
fn typed_elliptic_periapsis_to_sma() {
    let s = PeriapsisParam::try_new(1.0 * M, 0.5).unwrap();
    let ClassifiedPeriapsisParam::Elliptic(typed) = s.classify() else {
        panic!()
    };
    let sma = typed.to_semi_major_axis().unwrap();
    assert!((sma.semi_major_axis().value() - 2.0).abs() < 1e-12);
    assert_eq!(sma.eccentricity(), 0.5);
    assert_eq!(sma.kind(), ConicKind::Elliptic);
}

#[test]
fn typed_hyperbolic_periapsis_to_sma() {
    let s = PeriapsisParam::try_new(1.0 * M, 2.0).unwrap();
    let ClassifiedPeriapsisParam::Hyperbolic(typed) = s.classify() else {
        panic!()
    };
    let sma = typed.to_semi_major_axis().unwrap();
    assert!((sma.semi_major_axis().value() - 1.0).abs() < 1e-12);
    assert_eq!(sma.kind(), ConicKind::Hyperbolic);
}

#[test]
fn typed_sma_to_periapsis() {
    let s = SemiMajorAxisParam::try_new(2.0 * M, 0.5).unwrap();
    let ClassifiedSemiMajorAxisParam::Elliptic(typed) = s.classify() else {
        panic!()
    };
    let peri = typed.to_periapsis().unwrap();
    assert!((peri.periapsis_distance().value() - 1.0).abs() < 1e-12);
    assert_eq!(peri.kind(), ConicKind::Elliptic);
}

#[test]
fn periapsis_to_sma_preserves_orientation() {
    let ori = orientation();
    let conic = OrientedConic::new(PeriapsisParam::try_new(1.0 * M, 0.5).unwrap(), ori);
    let converted = conic.to_semi_major_axis().unwrap();
    assert_eq!(converted.orientation(), &ori);
}

#[test]
fn sma_to_periapsis_preserves_orientation() {
    let ori = orientation();
    let conic = OrientedConic::new(SemiMajorAxisParam::try_new(2.0 * M, 0.5).unwrap(), ori);
    let converted = conic.to_periapsis().unwrap();
    assert_eq!(converted.orientation(), &ori);
}

#[test]
fn periapsis_to_sma_parabolic_returns_none() {
    let ori = orientation();
    let conic = OrientedConic::new(PeriapsisParam::try_new(1.0 * M, 1.0).unwrap(), ori);
    assert!(conic.to_semi_major_axis().is_none());
}

#[test]
fn oriented_conic_kind_hyperbolic() {
    let conic = OrientedConic::new(
        PeriapsisParam::try_new(1.0 * M, 1.5).unwrap(),
        orientation(),
    );
    assert_eq!(conic.kind(), ConicKind::Hyperbolic);
}

#[test]
fn typed_oriented_elliptic_to_sma() {
    let ori = orientation();
    let ClassifiedPeriapsisParam::Elliptic(typed) =
        PeriapsisParam::try_new(1.0 * M, 0.5).unwrap().classify()
    else {
        panic!()
    };
    let conic = OrientedConic::new(typed, ori);
    let sma_conic = conic.to_semi_major_axis().unwrap();
    assert_eq!(sma_conic.orientation(), &ori);
    assert_eq!(sma_conic.kind(), ConicKind::Elliptic);
}

#[test]
fn periapsis_nextbefore_one_converts_to_sma() {
    // e = nextafter(1.0, -∞): classified Elliptic, must convert successfully
    let e = f64::from_bits(1.0f64.to_bits() - 1);
    assert!(e < 1.0);
    let s = PeriapsisParam::try_new(1.0 * M, e).unwrap();
    assert_eq!(s.kind(), ConicKind::Elliptic);
    let sma = s.to_semi_major_axis();
    assert!(sma.is_some(), "nextbefore(1.0) should convert to SMA");
    assert_eq!(sma.unwrap().kind(), ConicKind::Elliptic);
}

#[test]
fn periapsis_nextafter_one_converts_to_sma() {
    // e = nextafter(1.0, +∞): classified Hyperbolic, must convert successfully
    let e = f64::from_bits(1.0f64.to_bits() + 1);
    assert!(e > 1.0);
    let s = PeriapsisParam::try_new(1.0 * M, e).unwrap();
    assert_eq!(s.kind(), ConicKind::Hyperbolic);
    let sma = s.to_semi_major_axis();
    assert!(sma.is_some(), "nextafter(1.0) should convert to SMA");
    assert_eq!(sma.unwrap().kind(), ConicKind::Hyperbolic);
}

#[test]
fn periapsis_overflow_to_sma_returns_none() {
    // Large q with e just below 1 causes a / |1 - e| to overflow to inf
    let e = f64::from_bits(1.0f64.to_bits() - 1);
    let s = PeriapsisParam::try_new(f64::MAX * M, e).unwrap();
    assert!(s.to_semi_major_axis().is_none());
}

#[test]
fn sma_overflow_to_periapsis_returns_none() {
    // Large a * large |1 - e| overflows to inf
    let s = SemiMajorAxisParam::try_new(f64::MAX * M, 3.0).unwrap();
    assert!(s.to_periapsis().is_none());
}

#[test]
fn typed_sma_new_rejects_wrong_kind() {
    let inner = SemiMajorAxisParam::try_new(1.0 * M, 1.5).unwrap();
    assert!(TypedSemiMajorAxisParam::<_, Elliptic>::new(inner).is_none());
}

#[test]
fn typed_periapsis_has_inner_layout() {
    type Typed = TypedPeriapsisParam<Meter, Elliptic>;
    assert_eq!(
        core::mem::size_of::<Typed>(),
        core::mem::size_of::<PeriapsisParam<Meter>>()
    );
    assert_eq!(
        core::mem::align_of::<Typed>(),
        core::mem::align_of::<PeriapsisParam<Meter>>()
    );
}

#[test]
fn typed_sma_has_inner_layout() {
    type Typed = TypedSemiMajorAxisParam<Meter, Elliptic>;
    assert_eq!(
        core::mem::size_of::<Typed>(),
        core::mem::size_of::<SemiMajorAxisParam<Meter>>()
    );
    assert_eq!(
        core::mem::align_of::<Typed>(),
        core::mem::align_of::<SemiMajorAxisParam<Meter>>()
    );
}

#[test]
fn elliptic_periapsis_alias_is_usable() {
    let shape = PeriapsisParam::try_new(1.0 * M, 0.5).unwrap();
    let ClassifiedPeriapsisParam::Elliptic(typed) = shape.classify() else {
        panic!()
    };
    let conic: EllipticPeriapsis<_, TestFrame> = OrientedConic::new(typed, orientation());

    assert_eq!(conic.kind(), ConicKind::Elliptic);
    assert_eq!(conic.shape().eccentricity(), 0.5);
}

#[test]
fn elliptic_sma_alias_is_usable() {
    let shape = SemiMajorAxisParam::try_new(2.0 * M, 0.25).unwrap();
    let ClassifiedSemiMajorAxisParam::Elliptic(typed) = shape.classify() else {
        panic!()
    };
    let conic: EllipticSemiMajorAxis<_, TestFrame> = OrientedConic::new(typed, orientation());

    assert_eq!(conic.kind(), ConicKind::Elliptic);
    assert_eq!(conic.shape().semi_major_axis(), 2.0 * M);
}

// ==================== ConicValidationError::Display ====================

#[test]
fn error_display_invalid_eccentricity() {
    let msg = format!("{}", ConicValidationError::InvalidEccentricity);
    assert_eq!(msg, "invalid eccentricity");
}

#[test]
fn error_display_invalid_semi_major_axis() {
    let msg = format!("{}", ConicValidationError::InvalidSemiMajorAxis);
    assert_eq!(msg, "invalid semi-major axis");
}

#[test]
fn error_display_invalid_periapsis_distance() {
    let msg = format!("{}", ConicValidationError::InvalidPeriapsisDistance);
    assert_eq!(msg, "invalid periapsis distance");
}

#[test]
fn error_display_parabolic_semi_major_axis() {
    let msg = format!("{}", ConicValidationError::ParabolicSemiMajorAxis);
    assert!(msg.contains("parabolic"));
}

#[test]
fn error_display_invalid_orientation() {
    let msg = format!("{}", ConicValidationError::InvalidOrientation);
    assert_eq!(msg, "orientation angles must be finite");
}

#[test]
fn error_is_std_error() {
    let e: &dyn std::error::Error = &ConicValidationError::InvalidEccentricity;
    assert!(e.source().is_none());
}

// ==================== Parabolic conic kind ====================

#[test]
fn parabolic_conic_kind() {
    assert_eq!(Parabolic::conic_kind(), ConicKind::Parabolic);
}

// ==================== PeriapsisParam extra coverage ====================

#[test]
fn periapsis_new_unchecked_stores_values() {
    let p = PeriapsisParam::new_unchecked(2.0 * M, 0.6);
    assert_eq!(p.periapsis_distance(), 2.0 * M);
    assert_eq!(p.eccentricity(), 0.6);
}

#[test]
fn periapsis_to_semi_major_axis_elliptic() {
    // q = 0.5 AU, e = 0.5 → a = q / |1-e| = 0.5/0.5 = 1.0 AU
    use qtty::AU;
    let p = PeriapsisParam::try_new(0.5 * AU, 0.5).unwrap();
    let sma = p.to_semi_major_axis().unwrap();
    assert!((sma.semi_major_axis().value() - 1.0).abs() < 1e-10);
}

#[test]
fn periapsis_to_semi_major_axis_parabolic_returns_none() {
    let p = PeriapsisParam::try_new(1.0 * M, 1.0).unwrap();
    assert!(p.to_semi_major_axis().is_none());
}

#[test]
fn periapsis_shape_name() {
    assert_eq!(PeriapsisParam::<Meter>::shape_name(), "periapsis_distance");
}

#[test]
fn typed_periapsis_accessors() {
    let p = PeriapsisParam::try_new(3.0 * M, 0.7).unwrap();
    let ClassifiedPeriapsisParam::Elliptic(typed) = p.classify() else {
        panic!("expected elliptic");
    };
    assert_eq!(typed.periapsis_distance(), 3.0 * M);
    assert_eq!(typed.eccentricity(), 0.7);
    assert_eq!(typed.kind(), ConicKind::Elliptic);
    let inner = typed.into_inner();
    assert_eq!(inner.periapsis_distance(), 3.0 * M);
}

#[test]
fn typed_periapsis_to_semi_major_axis_elliptic() {
    let p = PeriapsisParam::try_new(0.5 * M, 0.5).unwrap();
    let ClassifiedPeriapsisParam::Elliptic(typed) = p.classify() else {
        panic!()
    };
    let sma = typed.to_semi_major_axis().unwrap();
    assert!((sma.semi_major_axis().value() - 1.0).abs() < 1e-10);
}

#[test]
fn typed_periapsis_to_semi_major_axis_hyperbolic() {
    let p = PeriapsisParam::try_new(2.0 * M, 2.0).unwrap();
    let ClassifiedPeriapsisParam::Hyperbolic(typed) = p.classify() else {
        panic!()
    };
    let sma = typed.to_semi_major_axis().unwrap();
    // a = q / |1-e| = 2.0 / 1.0 = 2.0
    assert!((sma.semi_major_axis().value() - 2.0).abs() < 1e-10);
}

// ==================== SemiMajorAxisParam extra coverage ====================

#[test]
fn sma_new_unchecked_stores_values() {
    let s = SemiMajorAxisParam::new_unchecked(5.0 * M, 0.3);
    assert_eq!(s.semi_major_axis(), 5.0 * M);
    assert_eq!(s.eccentricity(), 0.3);
}

#[test]
fn sma_shape_name() {
    assert_eq!(SemiMajorAxisParam::<Meter>::shape_name(), "semi_major_axis");
}

#[test]
fn sma_to_periapsis_elliptic() {
    // a = 1.0, e = 0.5 → q = a * |1 - e| = 0.5
    let s = SemiMajorAxisParam::try_new(1.0 * M, 0.5).unwrap();
    let p = s.to_periapsis().unwrap();
    assert!((p.periapsis_distance().value() - 0.5).abs() < 1e-10);
}

#[test]
fn sma_classify_elliptic() {
    let s = SemiMajorAxisParam::try_new(1.0 * M, 0.3).unwrap();
    assert!(matches!(
        s.classify(),
        ClassifiedSemiMajorAxisParam::Elliptic(_)
    ));
}

#[test]
fn sma_classify_hyperbolic() {
    let s = SemiMajorAxisParam::try_new(1.0 * M, 1.5).unwrap();
    assert!(matches!(
        s.classify(),
        ClassifiedSemiMajorAxisParam::Hyperbolic(_)
    ));
}

#[test]
fn typed_sma_new_accepts_matching_kind() {
    let s = SemiMajorAxisParam::try_new(1.0 * M, 0.3).unwrap();
    let typed = TypedSemiMajorAxisParam::<_, Elliptic>::new(s);
    assert!(typed.is_some());
}

#[test]
fn typed_sma_new_rejects_wrong_kind_v2() {
    let s = SemiMajorAxisParam::try_new(1.0 * M, 1.5).unwrap(); // hyperbolic
    let typed = TypedSemiMajorAxisParam::<_, Elliptic>::new(s);
    assert!(typed.is_none());
}

#[test]
fn typed_sma_accessors() {
    let s = SemiMajorAxisParam::try_new(4.0 * M, 0.2).unwrap();
    let ClassifiedSemiMajorAxisParam::Elliptic(typed) = s.classify() else {
        panic!()
    };
    assert_eq!(typed.semi_major_axis(), 4.0 * M);
    assert_eq!(typed.eccentricity(), 0.2);
    let inner = typed.into_inner();
    assert_eq!(inner.semi_major_axis(), 4.0 * M);
}

#[test]
fn typed_sma_to_periapsis_v2() {
    let s = SemiMajorAxisParam::try_new(2.0 * M, 0.5).unwrap();
    let ClassifiedSemiMajorAxisParam::Elliptic(typed) = s.classify() else {
        panic!()
    };
    let p = typed.to_periapsis().unwrap();
    // q = a * |1-e| = 2.0 * 0.5 = 1.0
    assert!((p.periapsis_distance().value() - 1.0).abs() < 1e-10);
}

// ==================== OrientedConic conversions ====================

#[test]
fn oriented_conic_periapsis_to_sma() {
    let shape = PeriapsisParam::try_new(0.5 * M, 0.5).unwrap();
    let oc = OrientedConic::new(shape, orientation());
    let sma_oc = oc.to_semi_major_axis().unwrap();
    assert!((sma_oc.shape().semi_major_axis().value() - 1.0).abs() < 1e-10);
}

#[test]
fn oriented_conic_sma_to_periapsis() {
    let shape = SemiMajorAxisParam::try_new(2.0 * M, 0.5).unwrap();
    let oc = OrientedConic::new(shape, orientation());
    let peri_oc = oc.to_periapsis().unwrap();
    // q = a * |1-e| = 2.0 * 0.5 = 1.0
    assert!((peri_oc.shape().periapsis_distance().value() - 1.0).abs() < 1e-10);
}

#[test]
fn oriented_conic_periapsis_parabolic_to_sma_is_none() {
    let shape = PeriapsisParam::try_new(1.0 * M, 1.0).unwrap();
    let oc = OrientedConic::new(shape, orientation());
    assert!(oc.to_semi_major_axis().is_none());
}

#[test]
fn oriented_conic_typed_elliptic_periapsis_to_sma() {
    let shape = PeriapsisParam::try_new(0.5 * M, 0.5).unwrap();
    let ClassifiedPeriapsisParam::Elliptic(typed) = shape.classify() else {
        panic!()
    };
    let oc = OrientedConic::new(typed, orientation());
    let sma = oc.to_semi_major_axis().unwrap();
    assert!((sma.shape().semi_major_axis().value() - 1.0).abs() < 1e-10);
}

#[test]
fn oriented_conic_typed_hyperbolic_periapsis_to_sma() {
    let shape = PeriapsisParam::try_new(2.0 * M, 2.0).unwrap();
    let ClassifiedPeriapsisParam::Hyperbolic(typed) = shape.classify() else {
        panic!()
    };
    let oc = OrientedConic::new(typed, orientation());
    let sma = oc.to_semi_major_axis().unwrap();
    assert!((sma.shape().semi_major_axis().value() - 2.0).abs() < 1e-10);
}

#[test]
fn oriented_conic_typed_sma_to_periapsis() {
    let shape = SemiMajorAxisParam::try_new(2.0 * M, 0.5).unwrap();
    let ClassifiedSemiMajorAxisParam::Elliptic(typed) = shape.classify() else {
        panic!()
    };
    let oc = OrientedConic::new(typed, orientation());
    let peri = oc.to_periapsis().unwrap();
    assert!((peri.shape().periapsis_distance().value() - 1.0).abs() < 1e-10);
}

// ==================== ConicOrientation extra coverage ====================

#[test]
fn orientation_new_unchecked_stores_values() {
    let o = ConicOrientation::<TestFrame>::new(10.0 * DEG, 20.0 * DEG, 30.0 * DEG);
    assert_eq!(o.inclination(), 10.0 * DEG);
    assert_eq!(o.longitude_of_ascending_node(), 20.0 * DEG);
    assert_eq!(o.argument_of_periapsis(), 30.0 * DEG);
}

#[test]
fn orientation_rejects_nan_argument_of_periapsis() {
    assert_eq!(
        ConicOrientation::<TestFrame>::try_new(
            Degrees::new(0.0),
            Degrees::new(0.0),
            Degrees::new(f64::NAN),
        ),
        Err(ConicValidationError::InvalidOrientation)
    );
}
