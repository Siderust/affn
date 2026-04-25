use affn::conic::{
    ClassifiedPeriapsisParam, ConicOrientation, ConicShape, ConicValidationError,
    EllipticPeriapsis, EllipticSemiMajorAxis, HyperbolicPeriapsis, HyperbolicSemiMajorAxis,
    OrientedConic, ParabolicPeriapsis, PeriapsisParam, SemiMajorAxisParam,
};
use affn::frames::ReferenceFrame;
#[allow(unused_imports)]
use qtty::angular::{Degrees, Radians};
#[allow(unused_imports)]
use qtty::length::{Kilometers, Meters};
use qtty::{DEG, M};
#[derive(Debug, Copy, Clone, PartialEq)]
struct Inertial;

impl ReferenceFrame for Inertial {
    fn frame_name() -> &'static str {
        "Inertial"
    }
}

fn main() {
    erased_runtime_shapes();
    classify_all_kinds();
    oriented_conics_and_aliases();
}

fn erased_runtime_shapes() {
    section("Erased Runtime Shapes");

    let periapsis = PeriapsisParam::try_new(7_000.0 * M, 0.42).expect("valid periapsis parameter");
    println!(
        "PeriapsisParam: q = {}, e = {}, kind = {:?}",
        periapsis.periapsis_distance(),
        periapsis.eccentricity(),
        periapsis.kind()
    );

    let semi_major_axis = periapsis
        .to_semi_major_axis()
        .expect("elliptic periapsis converts to semi-major axis");
    println!(
        "Converted to SemiMajorAxisParam: a = {}, kind = {:?}",
        semi_major_axis.semi_major_axis(),
        semi_major_axis.kind()
    );

    let hyperbolic = SemiMajorAxisParam::try_new(2.0 * M, 1.5).expect("valid hyperbolic shape");
    println!(
        "SemiMajorAxisParam: a = {}, e = {}, kind = {:?}",
        hyperbolic.semi_major_axis(),
        hyperbolic.eccentricity(),
        hyperbolic.kind()
    );

    match SemiMajorAxisParam::try_new(2.0 * M, 1.0) {
        Err(ConicValidationError::ParabolicSemiMajorAxis) => {
            println!("SemiMajorAxisParam rejects parabolic e == 1 at construction");
        }
        other => panic!("unexpected semi-major-axis classification result: {other:?}"),
    }
}

fn classify_all_kinds() {
    section("Classification To Typed Kinds");

    for eccentricity in [0.2, 1.0, 1.4] {
        let shape =
            PeriapsisParam::try_new(7_000.0 * M, eccentricity).expect("valid periapsis shape");

        match shape.classify() {
            ClassifiedPeriapsisParam::Elliptic(typed) => {
                let sma = typed
                    .to_semi_major_axis()
                    .expect("elliptic periapsis converts to semi-major axis");
                println!(
                    "Elliptic branch: q = {}, e = {}, a = {}",
                    typed.periapsis_distance(),
                    typed.eccentricity(),
                    sma.semi_major_axis()
                );
            }
            ClassifiedPeriapsisParam::Parabolic(typed) => {
                println!(
                    "Parabolic branch: q = {}, e = {} (no semi-major axis form)",
                    typed.periapsis_distance(),
                    typed.eccentricity()
                );
            }
            ClassifiedPeriapsisParam::Hyperbolic(typed) => {
                let sma = typed
                    .to_semi_major_axis()
                    .expect("hyperbolic periapsis converts to semi-major axis");
                println!(
                    "Hyperbolic branch: q = {}, e = {}, a = {}",
                    typed.periapsis_distance(),
                    typed.eccentricity(),
                    sma.semi_major_axis()
                );
            }
        }
    }
}

fn oriented_conics_and_aliases() {
    section("Oriented Conics And Aliases");

    let orientation = ConicOrientation::<Inertial>::try_new(28.5 * DEG, 40.0 * DEG, 15.0 * DEG)
        .expect("valid conic orientation");

    let elliptic_shape = PeriapsisParam::try_new(7_000.0 * M, 0.42).expect("valid elliptic shape");
    let ClassifiedPeriapsisParam::Elliptic(elliptic_typed) = elliptic_shape.classify() else {
        unreachable!("expected elliptic classification")
    };
    let elliptic: EllipticPeriapsis<_, Inertial> = OrientedConic::new(elliptic_typed, orientation);
    let elliptic_sma: EllipticSemiMajorAxis<_, Inertial> = elliptic
        .to_semi_major_axis()
        .expect("elliptic oriented conic converts to semi-major axis");

    println!(
        "EllipticPeriapsis: kind = {:?}, q = {}, i = {}",
        elliptic.kind(),
        elliptic.shape().periapsis_distance(),
        elliptic.orientation().inclination()
    );
    println!(
        "EllipticSemiMajorAxis: a = {}, same orientation = {}",
        elliptic_sma.shape().semi_major_axis(),
        elliptic_sma.orientation() == elliptic.orientation()
    );

    let parabolic_shape = PeriapsisParam::try_new(7_000.0 * M, 1.0).expect("valid parabolic shape");
    let ClassifiedPeriapsisParam::Parabolic(parabolic_typed) = parabolic_shape.classify() else {
        unreachable!("expected parabolic classification")
    };
    let parabolic: ParabolicPeriapsis<_, Inertial> =
        OrientedConic::new(parabolic_typed, orientation);

    println!(
        "ParabolicPeriapsis: kind = {:?}, q = {}, convertible to SMA = no",
        parabolic.kind(),
        parabolic.shape().periapsis_distance()
    );

    let hyperbolic_shape =
        PeriapsisParam::try_new(7_000.0 * M, 1.4).expect("valid hyperbolic shape");
    let ClassifiedPeriapsisParam::Hyperbolic(hyperbolic_typed) = hyperbolic_shape.classify() else {
        unreachable!("expected hyperbolic classification")
    };
    let hyperbolic: HyperbolicPeriapsis<_, Inertial> =
        OrientedConic::new(hyperbolic_typed, orientation);
    let hyperbolic_sma: HyperbolicSemiMajorAxis<_, Inertial> = hyperbolic
        .to_semi_major_axis()
        .expect("hyperbolic oriented conic converts to semi-major axis");

    println!(
        "HyperbolicPeriapsis: q = {}, node = {}",
        hyperbolic.shape().periapsis_distance(),
        hyperbolic.orientation().longitude_of_ascending_node()
    );
    println!(
        "HyperbolicSemiMajorAxis: a = {}, arg periapsis = {}",
        hyperbolic_sma.shape().semi_major_axis(),
        hyperbolic_sma.orientation().argument_of_periapsis()
    );
}

fn section(title: &str) {
    println!("\n== {title} ==");
}
