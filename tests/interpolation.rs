use affn::cartesian::{Position, Velocity};
use affn::interpolation::{
    CubicHermiteTable, HermiteNode, InterpolationError, ScalarCubicHermiteTable, ScalarHermiteNode,
};
use affn::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};
use qtty::unit::{Kilometer, Meter, Second};
use qtty::{Per, Quantity};

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct TestFrame;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct TestCenter;

type TestPosition = Position<TestCenter, TestFrame, Meter>;
type TestVelocity = Velocity<TestFrame, Meter>;
type TestKmPerSecond = Per<Kilometer, Second>;
type TestKilometerPosition = Position<TestCenter, TestFrame, Kilometer>;
type TestKilometerVelocity = Velocity<TestFrame, TestKmPerSecond>;

fn cubic(abscissa: f64) -> f64 {
    abscissa * abscissa * abscissa - 2.0 * abscissa * abscissa + abscissa + 1.0
}

fn cubic_derivative(abscissa: f64) -> f64 {
    3.0 * abscissa * abscissa - 4.0 * abscissa + 1.0
}

fn cubic_position(t: f64) -> TestKilometerPosition {
    TestKilometerPosition::new(cubic(t), -2.0 * cubic(t), 0.5 * cubic(t))
}

fn cubic_velocity(t: f64) -> TestKilometerVelocity {
    TestKilometerVelocity::new(
        Quantity::<TestKmPerSecond>::new(cubic_derivative(t)),
        Quantity::<TestKmPerSecond>::new(-2.0 * cubic_derivative(t)),
        Quantity::<TestKmPerSecond>::new(0.5 * cubic_derivative(t)),
    )
}

fn expect_table_error(
    result: Result<CubicHermiteTable<qtty::Second, TestKilometerPosition>, InterpolationError>,
) -> InterpolationError {
    match result {
        Ok(_) => panic!("table construction should fail"),
        Err(err) => err,
    }
}

fn expect_scalar_table_error(
    result: Result<ScalarCubicHermiteTable, InterpolationError>,
) -> InterpolationError {
    match result {
        Ok(_) => panic!("scalar table construction should fail"),
        Err(err) => err,
    }
}

#[test]
fn scalar_cubic_polynomial_is_reproduced() {
    let table = ScalarCubicHermiteTable::new(vec![
        ScalarHermiteNode {
            abscissa: -1.0,
            value: cubic(-1.0),
            derivative: cubic_derivative(-1.0),
        },
        ScalarHermiteNode {
            abscissa: 0.5,
            value: cubic(0.5),
            derivative: cubic_derivative(0.5),
        },
        ScalarHermiteNode {
            abscissa: 2.0,
            value: cubic(2.0),
            derivative: cubic_derivative(2.0),
        },
    ])
    .unwrap();

    for x in [-0.75, -0.1, 0.25, 1.25, 1.75] {
        let evaluated = table.evaluate(x).unwrap();
        assert!((evaluated.value - cubic(x)).abs() < 1e-12);
        assert!((evaluated.derivative - cubic_derivative(x)).abs() < 1e-12);
    }
}

#[test]
fn exact_node_evaluation_returns_node_value_and_derivative() {
    let table = ScalarCubicHermiteTable::new(vec![
        ScalarHermiteNode {
            abscissa: 0.0,
            value: 10.0,
            derivative: -3.0,
        },
        ScalarHermiteNode {
            abscissa: 2.0,
            value: 20.0,
            derivative: 4.0,
        },
    ])
    .unwrap();

    let evaluated = table.evaluate(2.0).unwrap();
    assert_eq!(evaluated.value, 20.0);
    assert_eq!(evaluated.derivative, 4.0);
}

#[test]
fn linear_motion_with_constant_velocity_is_exact() {
    let table = CubicHermiteTable::<f64, TestPosition>::new(vec![
        HermiteNode {
            abscissa: 0.0,
            value: TestPosition::new(1.0, 2.0, 3.0),
            derivative: TestVelocity::new(0.5, -1.0, 2.0),
        },
        HermiteNode {
            abscissa: 4.0,
            value: TestPosition::new(3.0, -2.0, 11.0),
            derivative: TestVelocity::new(0.5, -1.0, 2.0),
        },
    ])
    .unwrap();

    let evaluated = table.evaluate(1.5).unwrap();
    assert!((evaluated.value.x().value() - 1.75).abs() < 1e-12);
    assert!((evaluated.value.y().value() - 0.5).abs() < 1e-12);
    assert!((evaluated.value.z().value() - 6.0).abs() < 1e-12);
    assert!((evaluated.derivative.x().value() - 0.5).abs() < 1e-12);
    assert!((evaluated.derivative.y().value() + 1.0).abs() < 1e-12);
    assert!((evaluated.derivative.z().value() - 2.0).abs() < 1e-12);
}

#[test]
fn typed_abscissa_table_accepts_position_over_seconds_with_velocity() {
    let table = CubicHermiteTable::<qtty::Second, TestKilometerPosition>::new(vec![
        HermiteNode {
            abscissa: qtty::Second::new(0.0),
            value: TestKilometerPosition::new(1.0, 2.0, 3.0),
            derivative: TestKilometerVelocity::new(
                Quantity::<TestKmPerSecond>::new(0.5),
                Quantity::<TestKmPerSecond>::new(-1.0),
                Quantity::<TestKmPerSecond>::new(2.0),
            ),
        },
        HermiteNode {
            abscissa: qtty::Second::new(4.0),
            value: TestKilometerPosition::new(3.0, -2.0, 11.0),
            derivative: TestKilometerVelocity::new(
                Quantity::<TestKmPerSecond>::new(0.5),
                Quantity::<TestKmPerSecond>::new(-1.0),
                Quantity::<TestKmPerSecond>::new(2.0),
            ),
        },
    ])
    .unwrap();

    let evaluated = table.evaluate(qtty::Second::new(1.5)).unwrap();
    assert!((evaluated.value.x().value() - 1.75).abs() < 1e-12);
    assert!((evaluated.value.y().value() - 0.5).abs() < 1e-12);
    assert!((evaluated.value.z().value() - 6.0).abs() < 1e-12);
    assert!((evaluated.derivative.x().value() - 0.5).abs() < 1e-12);
    assert!((evaluated.derivative.y().value() + 1.0).abs() < 1e-12);
    assert!((evaluated.derivative.z().value() - 2.0).abs() < 1e-12);
}

#[test]
fn typed_abscissa_table_reproduces_cubic_position_over_seconds() {
    let table = CubicHermiteTable::<qtty::Second, TestKilometerPosition>::new(vec![
        HermiteNode {
            abscissa: qtty::Second::new(-1.0),
            value: cubic_position(-1.0),
            derivative: cubic_velocity(-1.0),
        },
        HermiteNode {
            abscissa: qtty::Second::new(0.5),
            value: cubic_position(0.5),
            derivative: cubic_velocity(0.5),
        },
        HermiteNode {
            abscissa: qtty::Second::new(2.0),
            value: cubic_position(2.0),
            derivative: cubic_velocity(2.0),
        },
    ])
    .unwrap();

    for t in [-0.75, -0.1, 0.25, 1.25, 1.75] {
        let evaluated = table.evaluate(qtty::Second::new(t)).unwrap();
        let expected_position = cubic_position(t);
        let expected_velocity = cubic_velocity(t);
        assert!((evaluated.value.x().value() - expected_position.x().value()).abs() < 1e-12);
        assert!((evaluated.value.y().value() - expected_position.y().value()).abs() < 1e-12);
        assert!((evaluated.value.z().value() - expected_position.z().value()).abs() < 1e-12);
        assert!((evaluated.derivative.x().value() - expected_velocity.x().value()).abs() < 1e-12);
        assert!((evaluated.derivative.y().value() - expected_velocity.y().value()).abs() < 1e-12);
        assert!((evaluated.derivative.z().value() - expected_velocity.z().value()).abs() < 1e-12);
    }
}

#[test]
fn typed_abscissa_table_rejects_non_finite_abscissa() {
    let err = expect_table_error(
        CubicHermiteTable::<qtty::Second, TestKilometerPosition>::new(vec![
            HermiteNode {
                abscissa: qtty::Second::new(f64::NAN),
                value: cubic_position(0.0),
                derivative: cubic_velocity(0.0),
            },
            HermiteNode {
                abscissa: qtty::Second::new(1.0),
                value: cubic_position(1.0),
                derivative: cubic_velocity(1.0),
            },
        ]),
    );

    assert_eq!(err, InterpolationError::NonFiniteAbscissa);
}

#[test]
fn typed_abscissa_table_rejects_non_finite_position_component() {
    let err = expect_table_error(
        CubicHermiteTable::<qtty::Second, TestKilometerPosition>::new(vec![
            HermiteNode {
                abscissa: qtty::Second::new(0.0),
                value: TestKilometerPosition::new(f64::NAN, 0.0, 0.0),
                derivative: cubic_velocity(0.0),
            },
            HermiteNode {
                abscissa: qtty::Second::new(1.0),
                value: cubic_position(1.0),
                derivative: cubic_velocity(1.0),
            },
        ]),
    );

    assert_eq!(err, InterpolationError::NonFiniteValue);
}

#[test]
fn typed_abscissa_table_rejects_duplicate_seconds() {
    let err = expect_table_error(
        CubicHermiteTable::<qtty::Second, TestKilometerPosition>::new(vec![
            HermiteNode {
                abscissa: qtty::Second::new(0.0),
                value: cubic_position(0.0),
                derivative: cubic_velocity(0.0),
            },
            HermiteNode {
                abscissa: qtty::Second::new(0.0),
                value: cubic_position(1.0),
                derivative: cubic_velocity(1.0),
            },
        ]),
    );

    assert_eq!(err, InterpolationError::DuplicateAbscissa);
}

#[test]
fn vector_dimensional_mul_and_div_quantity_work() {
    let velocity = TestKilometerVelocity::new(
        Quantity::<TestKmPerSecond>::new(2.0),
        Quantity::<TestKmPerSecond>::new(-3.0),
        Quantity::<TestKmPerSecond>::new(4.0),
    );
    let elapsed = qtty::Second::new(5.0);

    let displacement = velocity * elapsed;
    assert!((displacement.x().value() - 10.0).abs() < 1e-12);
    assert!((displacement.y().value() + 15.0).abs() < 1e-12);
    assert!((displacement.z().value() - 20.0).abs() < 1e-12);

    let recovered_velocity = displacement.div_quantity(elapsed);
    assert!((recovered_velocity.x().value() - 2.0).abs() < 1e-12);
    assert!((recovered_velocity.y().value() + 3.0).abs() < 1e-12);
    assert!((recovered_velocity.z().value() - 4.0).abs() < 1e-12);
}

#[test]
fn non_uniform_sample_spacing_works() {
    let table = ScalarCubicHermiteTable::new(vec![
        ScalarHermiteNode {
            abscissa: 0.0,
            value: cubic(0.0),
            derivative: cubic_derivative(0.0),
        },
        ScalarHermiteNode {
            abscissa: 0.25,
            value: cubic(0.25),
            derivative: cubic_derivative(0.25),
        },
        ScalarHermiteNode {
            abscissa: 2.5,
            value: cubic(2.5),
            derivative: cubic_derivative(2.5),
        },
    ])
    .unwrap();

    let evaluated = table.evaluate(1.75).unwrap();
    assert!((evaluated.value - cubic(1.75)).abs() < 1e-12);
    assert!((evaluated.derivative - cubic_derivative(1.75)).abs() < 1e-12);
}

#[test]
fn out_of_range_queries_return_error() {
    let table = ScalarCubicHermiteTable::new(vec![
        ScalarHermiteNode {
            abscissa: 0.0,
            value: 0.0,
            derivative: 1.0,
        },
        ScalarHermiteNode {
            abscissa: 1.0,
            value: 1.0,
            derivative: 1.0,
        },
    ])
    .unwrap();

    assert_eq!(
        table.evaluate(2.0),
        Err(InterpolationError::OutOfRange {
            requested_raw: 2.0,
            min_raw: 0.0,
            max_raw: 1.0
        })
    );
}

#[test]
fn duplicate_abscissae_are_rejected() {
    assert_eq!(
        expect_scalar_table_error(ScalarCubicHermiteTable::new(vec![
            ScalarHermiteNode {
                abscissa: 0.0,
                value: 0.0,
                derivative: 0.0,
            },
            ScalarHermiteNode {
                abscissa: 0.0,
                value: 1.0,
                derivative: 1.0,
            },
        ])),
        InterpolationError::DuplicateAbscissa
    );
}

#[test]
fn unsorted_abscissae_are_rejected() {
    assert_eq!(
        expect_scalar_table_error(ScalarCubicHermiteTable::new(vec![
            ScalarHermiteNode {
                abscissa: 1.0,
                value: 1.0,
                derivative: 1.0,
            },
            ScalarHermiteNode {
                abscissa: 0.0,
                value: 0.0,
                derivative: 0.0,
            },
        ])),
        InterpolationError::UnsortedAbscissa
    );
}
