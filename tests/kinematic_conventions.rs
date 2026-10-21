//! Independent checks of the documented free-vector/coordinate-velocity distinction.
use affn::matrix3::FrameMatrix3;
use affn::matrix6::FrameMatrix6;
use affn::ops::Rotation3;
use qtty::angular::Radians;

fn mat3_mul(a: [[f64; 3]; 3], b: [[f64; 3]; 3]) -> [[f64; 3]; 3] {
    let mut out = [[0.0; 3]; 3];
    for i in 0..3 {
        for k in 0..3 {
            for j in 0..3 {
                out[i][j] += a[i][k] * b[k][j];
            }
        }
    }
    out
}

fn mat3_transpose(a: [[f64; 3]; 3]) -> [[f64; 3]; 3] {
    core::array::from_fn(|i| core::array::from_fn(|j| a[j][i]))
}

fn mat3_add(a: [[f64; 3]; 3], b: [[f64; 3]; 3]) -> [[f64; 3]; 3] {
    core::array::from_fn(|i| core::array::from_fn(|j| a[i][j] + b[i][j]))
}

fn mat3_scale(a: [[f64; 3]; 3], scale: f64) -> [[f64; 3]; 3] {
    core::array::from_fn(|i| core::array::from_fn(|j| scale * a[i][j]))
}

fn apply_matrix(a: [[f64; 3]; 3], v: [f64; 3]) -> [f64; 3] {
    core::array::from_fn(|i| (0..3).map(|j| a[i][j] * v[j]).sum())
}

fn assert_matrix_close(actual: [[f64; 3]; 3], expected: [[f64; 3]; 3], tolerance: f64) {
    for i in 0..3 {
        for j in 0..3 {
            assert!(
                (actual[i][j] - expected[i][j]).abs() <= tolerance,
                "matrix mismatch at ({i}, {j}): {} != {}",
                actual[i][j],
                expected[i][j]
            );
        }
    }
}

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

#[test]
fn analytical_rotation_derivative_matches_finite_difference() {
    let omega: f64 = 0.7;
    let t: f64 = 0.4;
    let expected = [
        [-omega * (omega * t).sin(), -omega * (omega * t).cos(), 0.0],
        [omega * (omega * t).cos(), -omega * (omega * t).sin(), 0.0],
        [0.0, 0.0, 0.0],
    ];
    let h = 1e-6;
    let plus = *Rotation3::rz(Radians::new(omega * (t + h))).as_matrix();
    let minus = *Rotation3::rz(Radians::new(omega * (t - h))).as_matrix();
    let finite_difference = mat3_scale(mat3_add(plus, mat3_scale(minus, -1.0)), 0.5 / h);
    assert_matrix_close(finite_difference, expected, 1e-10);
}

#[test]
fn inverse_and_composition_derivatives_match_matrix_calculus() {
    let omega: f64 = 0.4;
    let nu: f64 = -0.6;
    let t: f64 = 0.8;
    let r = *Rotation3::rz(Radians::new(omega * t)).as_matrix();
    let s = *Rotation3::rx(Radians::new(nu * t)).as_matrix();
    let r_dot = [
        [-omega * (omega * t).sin(), -omega * (omega * t).cos(), 0.0],
        [omega * (omega * t).cos(), -omega * (omega * t).sin(), 0.0],
        [0.0, 0.0, 0.0],
    ];
    let s_dot = [
        [0.0, 0.0, 0.0],
        [0.0, -nu * (nu * t).sin(), -nu * (nu * t).cos()],
        [0.0, nu * (nu * t).cos(), -nu * (nu * t).sin()],
    ];
    let q = mat3_transpose(r);
    let q_dot = mat3_scale(mat3_mul(mat3_mul(q, r_dot), q), -1.0);
    let expected_q_dot = [
        [-omega * (omega * t).sin(), omega * (omega * t).cos(), 0.0],
        [-omega * (omega * t).cos(), -omega * (omega * t).sin(), 0.0],
        [0.0, 0.0, 0.0],
    ];
    assert_matrix_close(q_dot, expected_q_dot, 1e-14);

    let t_dot = mat3_add(mat3_mul(s_dot, r), mat3_mul(s, r_dot));
    let h = 1e-6;
    let composed = |time: f64| {
        *Rotation3::rx(Radians::new(nu * time))
            .compose(&Rotation3::rz(Radians::new(omega * time)))
            .as_matrix()
    };
    let finite_difference = mat3_scale(
        mat3_add(composed(t + h), mat3_scale(composed(t - h), -1.0)),
        0.5 / h,
    );
    assert_matrix_close(finite_difference, t_dot, 1e-10);
}

#[test]
fn kinematic_state_round_trip_uses_inverse_derivative() {
    let omega: f64 = 0.3;
    let t: f64 = 0.9;
    let r = *Rotation3::rz(Radians::new(omega * t)).as_matrix();
    let q = mat3_transpose(r);
    let r_dot = [
        [-omega * (omega * t).sin(), -omega * (omega * t).cos(), 0.0],
        [omega * (omega * t).cos(), -omega * (omega * t).sin(), 0.0],
        [0.0, 0.0, 0.0],
    ];
    let q_dot = mat3_scale(mat3_mul(mat3_mul(q, r_dot), q), -1.0);
    let position = [2.0, -1.0, 4.0];
    let velocity = [-0.4, 0.8, 0.2];
    let position_b = apply_matrix(r, position);
    let velocity_b: [f64; 3] = {
        let rotated = apply_matrix(r, velocity);
        let derivative = apply_matrix(r_dot, position);
        core::array::from_fn(|i| rotated[i] + derivative[i])
    };
    let recovered_position = apply_matrix(q, position_b);
    let recovered_velocity: [f64; 3] = {
        let rotated = apply_matrix(q, velocity_b);
        let derivative = apply_matrix(q_dot, position_b);
        core::array::from_fn(|i| rotated[i] + derivative[i])
    };
    for i in 0..3 {
        assert!((recovered_position[i] - position[i]).abs() < 1e-14);
        assert!((recovered_velocity[i] - velocity[i]).abs() < 1e-14);
    }
}

#[test]
fn full_kinematic_jacobian_transforms_covariance() {
    #[derive(Debug, Copy, Clone)]
    struct FrameA;
    #[derive(Debug, Copy, Clone)]
    struct FrameB;

    let omega: f64 = 0.5;
    let t: f64 = 0.6;
    let rotation = Rotation3::rz(Radians::new(omega * t));
    let r = *rotation.as_matrix();
    let r_dot = [
        [-omega * (omega * t).sin(), -omega * (omega * t).cos(), 0.0],
        [omega * (omega * t).cos(), -omega * (omega * t).sin(), 0.0],
        [0.0, 0.0, 0.0],
    ];
    let jacobian = FrameMatrix6::<FrameA>::from_blocks(
        FrameMatrix3::from_array(r),
        FrameMatrix3::zero(),
        FrameMatrix3::from_array(r_dot),
        FrameMatrix3::from_array(r),
    );
    let covariance = FrameMatrix6::<FrameA>::from_array({
        let mut p = [[0.0; 6]; 6];
        p[0][0] = 4.0;
        p[1][1] = 9.0;
        p[2][2] = 1.0;
        p
    });
    let transformed: FrameMatrix6<FrameB> = jacobian
        .mat_mul(&covariance)
        .mat_mul(&jacobian.transpose())
        .relabel();

    let expected_velocity_covariance = mat3_mul(
        mat3_mul(r_dot, *covariance.top_left().as_array()),
        mat3_transpose(r_dot),
    );
    assert_matrix_close(
        *transformed.bottom_right().as_array(),
        expected_velocity_covariance,
        1e-14,
    );
    assert!(transformed.bottom_right().as_array()[0][0] > 0.0);
    assert!(transformed.bottom_left().as_array()[0][0].abs() > 0.0);
}
