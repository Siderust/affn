use super::*;
use qtty::*;

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
