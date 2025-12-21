use affn::cartesian::{Displacement, Position};
use affn::prelude::*;
use qtty::*;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct LocalFrame;

#[derive(Clone, Debug, Default, PartialEq)]
struct Observer {
    lat_deg: f64,
    lon_deg: f64,
}

#[derive(Debug, Copy, Clone, ReferenceCenter)]
#[center(params = Observer)]
struct Topocentric;

fn main() {
    let site = Observer {
        lat_deg: 41.0,
        lon_deg: 2.0,
    };

    let a =
        Position::<Topocentric, LocalFrame, Meter>::new_with_params(site.clone(), 0.0, 0.0, 0.0);
    let b =
        Position::<Topocentric, LocalFrame, Meter>::new_with_params(site.clone(), 10.0, 0.0, 0.0);

    let d: Displacement<LocalFrame, Meter> = &b - &a;
    println!("distance = {}", d.magnitude());
    assert!((d.magnitude().value() - 10.0).abs() < 1e-12);
}
