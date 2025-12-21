use affn::cartesian::Position as CPos;
use affn::centers::ReferenceCenter;
use affn::frames::ReferenceFrame;
use affn::spherical::Position as SPos;
use qtty::*;

#[derive(Debug, Copy, Clone)]
struct Frame;
impl ReferenceFrame for Frame {
    fn frame_name() -> &'static str {
        "Frame"
    }
}

#[derive(Debug, Copy, Clone)]
struct Center;
impl ReferenceCenter for Center {
    type Params = ();
    fn center_name() -> &'static str {
        "Center"
    }
}

fn main() {
    let cart = CPos::<Center, Frame, Meter>::new(1.0, 1.0, 1.0);
    let sph: SPos<Center, Frame, Meter> = cart.to_spherical();
    println!("spherical = {}", sph);

    let back: CPos<Center, Frame, Meter> = CPos::from_spherical(&sph);
    println!("cartesian (back) = {}", back);

    assert!((back.x().value() - cart.x().value()).abs() < 1e-10);
    assert!((back.y().value() - cart.y().value()).abs() < 1e-10);
    assert!((back.z().value() - cart.z().value()).abs() < 1e-10);
}
