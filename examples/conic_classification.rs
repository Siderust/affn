use affn::conic::{ConicKind, ConicShape, PeriapsisParam, SemiMajorAxisParam};
use qtty::*;

fn main() {
    let periapsis = PeriapsisParam::try_new(1.0 * M, 0.5).expect("valid periapsis parameter");
    println!(
        "periapsis distance = {}, eccentricity = {}, kind = {:?}",
        periapsis.periapsis_distance(),
        periapsis.eccentricity(),
        periapsis.kind()
    );

    let classified = periapsis.classify();
    match classified {
        affn::conic::ClassifiedPeriapsisParam::Elliptic(typed) => {
            let sma = typed.to_semi_major_axis().expect("elliptic orbit converts to SMA");
            println!(
                "elliptic semi-major axis = {}, kind = {:?}",
                sma.semi_major_axis(),
                sma.kind()
            );
        }
        affn::conic::ClassifiedPeriapsisParam::Parabolic(typed) => {
            println!("parabolic orbit, periapsis = {}", typed.periapsis_distance());
        }
        affn::conic::ClassifiedPeriapsisParam::Hyperbolic(typed) => {
            println!("hyperbolic orbit, periapsis = {}", typed.periapsis_distance());
        }
    }

    let sma = SemiMajorAxisParam::try_new(2.0 * M, 1.5).expect("valid semi-major axis parameter");
    println!(
        "semi-major axis = {}, eccentricity = {}, kind = {:?}",
        sma.semi_major_axis(),
        sma.eccentricity(),
        sma.kind()
    );
    assert_eq!(sma.kind(), ConicKind::Hyperbolic);
}