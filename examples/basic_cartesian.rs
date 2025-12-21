use affn::cartesian::{line_of_sight, Displacement, Position};
use affn::centers::ReferenceCenter;
use affn::frames::ReferenceFrame;
use qtty::*;

#[derive(Debug, Copy, Clone)]
struct World;
impl ReferenceFrame for World {
    fn frame_name() -> &'static str {
        "World"
    }
}

#[derive(Debug, Copy, Clone)]
struct Origin;
impl ReferenceCenter for Origin {
    type Params = ();
    fn center_name() -> &'static str {
        "Origin"
    }
}

fn main() {
    let observer = Position::<Origin, World, Meter>::new(0.0, 0.0, 0.0);
    let target = Position::<Origin, World, Meter>::new(3.0, 4.0, 0.0);

    let displacement: Displacement<World, Meter> = &target - &observer;
    println!("displacement = {}", displacement);
    println!("distance = {}", displacement.magnitude());

    let direction = line_of_sight(&observer, &target);
    println!("line-of-sight direction = {}", direction);

    let translated = observer + displacement;
    assert!((translated.x().value() - target.x().value()).abs() < 1e-12);
    assert!((translated.y().value() - target.y().value()).abs() < 1e-12);
    assert!((translated.z().value() - target.z().value()).abs() < 1e-12);
}
