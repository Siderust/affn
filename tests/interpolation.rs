use affn::cartesian::{Position, Velocity};
use affn::interpolation::{
    CubicHermiteQuantityTable, CubicHermiteSpline, CubicHermiteTable, HermiteNode, HermiteSample,
    InterpolationError, QuantityHermiteNode,
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

fn cubic(x: f64) -> f64 {
    x * x * x - 2.0 * x * x + x + 1.0
}

fn cubic_derivative(x: f64) -> f64 {
    3.0 * x * x - 4.0 * x + 1.0
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

#[test]
fn scalar_cubic_polynomial_is_reproduced() {
    let spline = CubicHermiteSpline::new(vec![
        HermiteSample {
            x: -1.0,
            y: cubic(-1.0),
            dydx: cubic_derivative(-1.0),
        },
        HermiteSample {
            x: 0.5,
            y: cubic(0.5),
            dydx: cubic_derivative(0.5),
        },
        HermiteSample {
            x: 2.0,
            y: cubic(2.0),
            dydx: cubic_derivative(2.0),
        },
    ])
    .unwrap();

    for x in [-0.75, -0.1, 0.25, 1.25, 1.75] {
        let evaluated = spline.evaluate(x).unwrap();
        assert!((evaluated.value - cubic(x)).abs() < 1e-12);
        assert!((evaluated.derivative - cubic_derivative(x)).abs() < 1e-12);
    }
}

#[test]
fn exact_node_evaluation_returns_node_value_and_derivative() {
    let spline = CubicHermiteSpline::new(vec![
        HermiteSample {
            x: 0.0,
            y: 10.0,
            dydx: -3.0,
        },
        HermiteSample {
            x: 2.0,
            y: 20.0,
            dydx: 4.0,
        },
    ])
    .unwrap();

    let evaluated = spline.evaluate(2.0).unwrap();
    assert_eq!(evaluated.value, 20.0);
    assert_eq!(evaluated.derivative, 4.0);
}

#[test]
fn linear_motion_with_constant_velocity_is_exact() {
    let table = CubicHermiteTable::new(vec![
        HermiteNode {
            x: 0.0,
            value: TestPosition::new(1.0, 2.0, 3.0),
            derivative: TestVelocity::new(0.5, -1.0, 2.0),
        },
        HermiteNode {
            x: 4.0,
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
fn quantity_table_accepts_position_over_seconds_with_velocity() {
    let table = CubicHermiteQuantityTable::<Second, TestKilometerPosition>::new(vec![
        QuantityHermiteNode {
            x: qtty::Second::new(0.0),
            value: TestKilometerPosition::new(1.0, 2.0, 3.0),
            derivative: TestKilometerVelocity::new(
                Quantity::<TestKmPerSecond>::new(0.5),
                Quantity::<TestKmPerSecond>::new(-1.0),
                Quantity::<TestKmPerSecond>::new(2.0),
            ),
        },
        QuantityHermiteNode {
            x: qtty::Second::new(4.0),
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
fn quantity_table_reproduces_cubic_position_over_seconds() {
    let table = CubicHermiteQuantityTable::<Second, TestKilometerPosition>::new(vec![
        QuantityHermiteNode {
            x: qtty::Second::new(-1.0),
            value: cubic_position(-1.0),
            derivative: cubic_velocity(-1.0),
        },
        QuantityHermiteNode {
            x: qtty::Second::new(0.5),
            value: cubic_position(0.5),
            derivative: cubic_velocity(0.5),
        },
        QuantityHermiteNode {
            x: qtty::Second::new(2.0),
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
fn non_uniform_sample_spacing_works() {
    let spline = CubicHermiteSpline::new(vec![
        HermiteSample {
            x: 0.0,
            y: cubic(0.0),
            dydx: cubic_derivative(0.0),
        },
        HermiteSample {
            x: 0.25,
            y: cubic(0.25),
            dydx: cubic_derivative(0.25),
        },
        HermiteSample {
            x: 2.5,
            y: cubic(2.5),
            dydx: cubic_derivative(2.5),
        },
    ])
    .unwrap();

    let evaluated = spline.evaluate(1.75).unwrap();
    assert!((evaluated.value - cubic(1.75)).abs() < 1e-12);
    assert!((evaluated.derivative - cubic_derivative(1.75)).abs() < 1e-12);
}

#[test]
fn out_of_range_queries_return_error() {
    let spline = CubicHermiteSpline::new(vec![
        HermiteSample {
            x: 0.0,
            y: 0.0,
            dydx: 1.0,
        },
        HermiteSample {
            x: 1.0,
            y: 1.0,
            dydx: 1.0,
        },
    ])
    .unwrap();

    assert_eq!(
        spline.evaluate(2.0),
        Err(InterpolationError::OutOfRange {
            x: 2.0,
            min: 0.0,
            max: 1.0
        })
    );
}

#[test]
fn duplicate_abscissae_are_rejected() {
    assert_eq!(
        CubicHermiteSpline::new(vec![
            HermiteSample {
                x: 0.0,
                y: 0.0,
                dydx: 0.0,
            },
            HermiteSample {
                x: 0.0,
                y: 1.0,
                dydx: 1.0,
            },
        ]),
        Err(InterpolationError::DuplicateAbscissa)
    );
}

#[test]
fn unsorted_abscissae_are_rejected() {
    assert_eq!(
        CubicHermiteSpline::new(vec![
            HermiteSample {
                x: 1.0,
                y: 1.0,
                dydx: 1.0,
            },
            HermiteSample {
                x: 0.0,
                y: 0.0,
                dydx: 0.0,
            },
        ]),
        Err(InterpolationError::UnsortedAbscissa)
    );
}
