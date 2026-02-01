// Run with:
//   cargo run --example serde_roundtrip --features serde

#[cfg(not(feature = "serde"))]
fn main() {
    eprintln!("This example requires the `serde` feature.\n\nRun:\n  cargo run --example serde_roundtrip --features serde");
}

#[cfg(feature = "serde")]
fn main() {
    use affn::cartesian::{Direction as CartesianDirection, Position as CartesianPosition, Vector};
    use affn::centers::ReferenceCenter;
    use affn::frames::{ReferenceFrame, SphericalNaming};
    use affn::spherical::{Direction as SphericalDirection, Position as SphericalPosition};
    use qtty::*;

    #[derive(Debug, Copy, Clone, PartialEq)]
    struct World;
    impl ReferenceFrame for World {
        fn frame_name() -> &'static str {
            "World"
        }
    }
    impl SphericalNaming for World {
        fn polar_name() -> &'static str {
            "polar"
        }
        fn azimuth_name() -> &'static str {
            "azimuth"
        }
    }

    #[derive(Debug, Copy, Clone, PartialEq)]
    struct Origin;
    impl ReferenceCenter for Origin {
        type Params = ();
        fn center_name() -> &'static str {
            "Origin"
        }
    }

    // Cartesian position
    let p = CartesianPosition::<Origin, World, Meter>::new(1.0, 2.0, 3.0);
    let p_json = serde_json::to_string_pretty(&p).expect("serialize cartesian position");
    let p_back: CartesianPosition<Origin, World, Meter> =
        serde_json::from_str(&p_json).expect("deserialize cartesian position");
    assert_eq!(p.x(), p_back.x());
    assert_eq!(p.y(), p_back.y());
    assert_eq!(p.z(), p_back.z());

    // Cartesian vector
    let v = Vector::<World, Kilometer>::new(10.0, 20.0, 30.0);
    let v_json = serde_json::to_string(&v).expect("serialize vector");
    let v_back: Vector<World, Kilometer> =
        serde_json::from_str(&v_json).expect("deserialize vector");
    assert_eq!(v.x(), v_back.x());
    assert_eq!(v.y(), v_back.y());
    assert_eq!(v.z(), v_back.z());

    // Cartesian direction (normalized)
    let d = CartesianDirection::<World>::new(1.0, 2.0, 2.0);
    let d_json = serde_json::to_string(&d).expect("serialize cartesian direction");
    let d_back: CartesianDirection<World> =
        serde_json::from_str(&d_json).expect("deserialize cartesian direction");
    let eps = 1e-12;
    assert!((d.x() - d_back.x()).abs() < eps);
    assert!((d.y() - d_back.y()).abs() < eps);
    assert!((d.z() - d_back.z()).abs() < eps);

    // Spherical position
    let sp = SphericalPosition::<Origin, World, Meter>::new_raw(45.0 * DEG, 30.0 * DEG, 100.0 * M);
    let sp_json = serde_json::to_string(&sp).expect("serialize spherical position");
    let sp_back: SphericalPosition<Origin, World, Meter> =
        serde_json::from_str(&sp_json).expect("deserialize spherical position");
    assert!((sp.polar.value() - sp_back.polar.value()).abs() < eps);
    assert!((sp.azimuth.value() - sp_back.azimuth.value()).abs() < eps);
    assert_eq!(sp.distance, sp_back.distance);

    // Spherical direction
    let sd = SphericalDirection::<World>::new(10.0 * DEG, 350.0 * DEG);
    let sd_json = serde_json::to_string_pretty(&sd).expect("serialize spherical direction");
    let sd_back: SphericalDirection<World> =
        serde_json::from_str(&sd_json).expect("deserialize spherical direction");
    assert!((sd.polar.value() - sd_back.polar.value()).abs() < eps);
    assert!((sd.azimuth.value() - sd_back.azimuth.value()).abs() < eps);

    println!("Cartesian Position JSON:\n{p_json}\n");
    println!("Spherical Direction JSON:\n{sd_json}\n");
    println!("Serde round-trip OK");
}
