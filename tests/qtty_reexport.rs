//! Downstream-style usage via `affn::qtty` without a direct `qtty` dependency.

use affn::cartesian::{Displacement, Position};
use affn::centers::ReferenceCenter;
use affn::frames::ReferenceFrame;
use affn::qtty::units::Meter;
use affn::qtty::{Quantity, M};

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

#[test]
fn construct_affn_types_via_reexported_qtty() {
    let a = Position::<Origin, World, Meter>::new(0.0 * M, 0.0 * M, 0.0 * M);
    let offset: Quantity<Meter> = 5.0 * M;
    let b = Position::<Origin, World, Meter>::new(offset, 0.0 * M, 0.0 * M);

    let d: Displacement<World, Meter> = b - a;
    assert!((d.magnitude().value() - 5.0).abs() < 1e-12);
}
