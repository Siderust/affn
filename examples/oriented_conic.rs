use affn::conic::{ConicOrientation, OrientedConic, PeriapsisParam};
use affn::frames::ReferenceFrame;
use qtty::*;

#[derive(Debug, Copy, Clone, PartialEq)]
struct Inertial;

impl ReferenceFrame for Inertial {
    fn frame_name() -> &'static str {
        "Inertial"
    }
}

fn main() {
    let orientation = ConicOrientation::<Inertial>::new(28.5 * DEG, 40.0 * DEG, 15.0 * DEG);
    let periapsis = PeriapsisParam::try_new(7_000.0 * M, 0.42).expect("valid periapsis parameter");
    let conic = OrientedConic::new(periapsis, orientation);

    println!("kind = {:?}", conic.kind());
    println!("periapsis distance = {}", conic.shape().periapsis_distance());
    println!("inclination = {}", conic.orientation().inclination());

    let semi_major_axis = conic.to_semi_major_axis().expect("elliptic orbit converts to SMA");
    println!("semi-major axis = {}", semi_major_axis.shape().semi_major_axis());
    assert_eq!(semi_major_axis.orientation(), conic.orientation());
}