use affn::conic::{ClassifiedPeriapsisParam, ConicKind, ConicShape, PeriapsisParam};
use qtty::*;

fn main() {
    elliptic_example();
    parabolic_example();
    hyperbolic_example();
}

fn elliptic_example() {
    let shape = PeriapsisParam::try_new(7_000.0 * M, 0.2).expect("valid elliptic periapsis");
    assert_eq!(shape.kind(), ConicKind::Elliptic);

    let ClassifiedPeriapsisParam::Elliptic(typed) = shape.classify() else {
        unreachable!("expected elliptic classification")
    };
    let sma = typed
        .to_semi_major_axis()
        .expect("elliptic periapsis converts to semi-major axis");

    println!(
        "Elliptic: q = {}, e = {}, a = {}",
        typed.periapsis_distance(),
        typed.eccentricity(),
        sma.semi_major_axis()
    );
}

fn parabolic_example() {
    let shape = PeriapsisParam::try_new(7_000.0 * M, 1.0).expect("valid parabolic periapsis");
    assert_eq!(shape.kind(), ConicKind::Parabolic);

    let ClassifiedPeriapsisParam::Parabolic(typed) = shape.classify() else {
        unreachable!("expected parabolic classification")
    };

    println!(
        "Parabolic: q = {}, e = {} (no semi-major axis form)",
        typed.periapsis_distance(),
        typed.eccentricity()
    );
}

fn hyperbolic_example() {
    let shape = PeriapsisParam::try_new(7_000.0 * M, 1.4).expect("valid hyperbolic periapsis");
    assert_eq!(shape.kind(), ConicKind::Hyperbolic);

    let ClassifiedPeriapsisParam::Hyperbolic(typed) = shape.classify() else {
        unreachable!("expected hyperbolic classification")
    };
    let sma = typed
        .to_semi_major_axis()
        .expect("hyperbolic periapsis converts to semi-major axis");

    println!(
        "Hyperbolic: q = {}, e = {}, a = {}",
        typed.periapsis_distance(),
        typed.eccentricity(),
        sma.semi_major_axis()
    );
}