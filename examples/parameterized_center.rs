use affn::cartesian::Position;
use affn::prelude::*;
#[allow(unused_imports)]
use qtty::angular::{Degrees, Radians};
#[allow(unused_imports)]
use qtty::length::{Kilometers, Meters};
use qtty::units::Meter;
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

    // For parameterized centers (Params != ()), use checked_sub or try_distance_to.
    // The `-` operator is restricted to centers with Params = () to prevent
    // silent param-mismatch bugs at compile time.
    let d = b
        .checked_sub(&a)
        .expect("same observer site, should not fail");
    println!("distance = {}", d.magnitude());
    assert!((d.magnitude().value() - 10.0).abs() < 1e-12);

    // Mismatched sites produce an error instead of a panic:
    let other_site = Observer {
        lat_deg: 52.0,
        lon_deg: 4.0,
    };
    let c = Position::<Topocentric, LocalFrame, Meter>::new_with_params(other_site, 5.0, 0.0, 0.0);
    assert!(b.checked_sub(&c).is_err(), "different sites => Err");
}
