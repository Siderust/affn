//! Independent checks of the documented free-vector/coordinate-velocity distinction.
use affn::ops::Rotation3;
use qtty::angular::Radians;

#[test]
fn rotating_coordinates_need_a_velocity_term_and_round_trip() {
    // Rz(+omega*t) is an explicitly chosen coordinate map, not an Earth convention.
    let omega = 0.2;
    let t = 0.7;
    let r = [3.0, -4.0, 2.0];
    let v = [0.5, 0.1, -0.3];
    let rotation = Rotation3::rz(Radians::new(omega * t));
    let rb = rotation.apply_array(r);
    let free_v = rotation.apply_array(v);
    let vb = [
        free_v[0] - omega * rb[1],
        free_v[1] + omega * rb[0],
        free_v[2],
    ];
    assert!((vb[0] - free_v[0]).abs() > 0.1);
    // Differentiate the independently evaluated trajectory R(t+h)*(r+h*v).
    let h = 1e-5;
    let eval = |dt: f64| {
        Rotation3::rz(Radians::new(omega * (t + dt)))
            .apply_array(core::array::from_fn(|i| r[i] + dt * v[i]))
    };
    let plus = eval(h);
    let minus = eval(-h);
    for i in 0..3 {
        assert!(((plus[i] - minus[i]) / (2.0 * h) - vb[i]).abs() < 1e-9);
    }
    let recovered_r = rotation.inverse().apply_array(rb);
    let recovered_v =
        rotation
            .inverse()
            .apply_array([vb[0] + omega * rb[1], vb[1] - omega * rb[0], vb[2]]);
    for i in 0..3 {
        assert!((recovered_r[i] - r[i]).abs() < 1e-14);
        assert!((recovered_v[i] - v[i]).abs() < 1e-14);
    }
}

#[test]
fn constant_rotations_compose_and_invert_for_independent_vectors() {
    let a = Rotation3::rx(Radians::new(0.3));
    let b = Rotation3::rz(Radians::new(-0.9));
    let r = [2.0, 3.0, -5.0];
    let composed = b.compose(&a);
    let sequential = b.apply_array(a.apply_array(r));
    let actual = composed.apply_array(r);
    let back = composed.inverse().apply_array(actual);
    for i in 0..3 {
        assert!((actual[i] - sequential[i]).abs() < 1e-14);
        assert!((back[i] - r[i]).abs() < 1e-14);
        assert_eq!(Rotation3::IDENTITY.apply_array(r)[i], r[i]);
    }
}
