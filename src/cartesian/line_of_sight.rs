//! Line-of-sight computation between positions.

use super::{Direction, Displacement, Position};
use crate::centers::ReferenceCenter;
use crate::frames::ReferenceFrame;
use qtty::{LengthUnit, Quantity};

/// Computes the line-of-sight direction from an observer to a target.
///
/// This is the mathematically correct way to obtain an observer-dependent
/// direction. The result is a unit direction (free vector) pointing from
/// the observer position toward the target position.
///
/// # Mathematical Definition
///
/// ```text
/// displacement = target - observer
/// direction = normalize(displacement)
/// ```
///
/// # Requirements
///
/// Both positions must be in the **same center and frame**. If they are not,
/// convert them first in your domain layer (where you define the semantics of those transforms).
///
/// # Example
///
/// ```rust
/// use affn::cartesian::{line_of_sight, Position, Direction};
/// use affn::frames::ReferenceFrame;
/// use affn::centers::ReferenceCenter;
/// use qtty::*;
///
/// #[derive(Debug, Copy, Clone)]
/// struct WorldFrame;
/// impl ReferenceFrame for WorldFrame {
///     fn frame_name() -> &'static str { "WorldFrame" }
/// }
///
/// #[derive(Debug, Copy, Clone)]
/// struct WorldOrigin;
/// impl ReferenceCenter for WorldOrigin {
///     type Params = ();
///     fn center_name() -> &'static str { "WorldOrigin" }
/// }
///
/// let observer = Position::<WorldOrigin, WorldFrame, Meter>::new(0.0, 0.0, 0.0);
/// let target = Position::<WorldOrigin, WorldFrame, Meter>::new(1.0, 1.0, 0.0);
///
/// let los: Direction<WorldFrame> = line_of_sight(&observer, &target);
/// ```
///
/// # Panics
///
/// Panics if the observer and target positions are identical (zero displacement).
#[inline]
pub fn line_of_sight<C, F, U>(
    observer: &Position<C, F, U>,
    target: &Position<C, F, U>,
) -> Direction<F>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    // Position - Position -> Displacement
    let displacement: Displacement<F, U> = target - observer;

    // normalize(Displacement) -> Direction
    displacement
        .normalize()
        .expect("line_of_sight requires distinct observer and target positions")
}

/// Computes the line-of-sight direction and distance from an observer to a target.
///
/// Returns both the unit direction and the distance (magnitude of the displacement).
/// This is useful when you need both the pointing direction and the range.
///
/// # Example
///
/// ```rust
/// use affn::cartesian::{line_of_sight_with_distance, Position};
/// use affn::frames::ReferenceFrame;
/// use affn::centers::ReferenceCenter;
/// use qtty::*;
///
/// #[derive(Debug, Copy, Clone)]
/// struct WorldFrame;
/// impl ReferenceFrame for WorldFrame {
///     fn frame_name() -> &'static str { "WorldFrame" }
/// }
///
/// #[derive(Debug, Copy, Clone)]
/// struct WorldOrigin;
/// impl ReferenceCenter for WorldOrigin {
///     type Params = ();
///     fn center_name() -> &'static str { "WorldOrigin" }
/// }
///
/// let observer = Position::<WorldOrigin, WorldFrame, Meter>::new(0.0, 0.0, 0.0);
/// let target = Position::<WorldOrigin, WorldFrame, Meter>::new(3.0, 4.0, 0.0);
///
/// let (dir, dist) = line_of_sight_with_distance(&observer, &target);
/// assert!((dist.value() - 5.0).abs() < 1e-10);
/// assert!((dir.x() - 0.6).abs() < 1e-10);
/// assert!((dir.y() - 0.8).abs() < 1e-10);
/// ```
///
/// # Panics
///
/// Panics if the observer and target positions are identical.
#[inline]
pub fn line_of_sight_with_distance<C, F, U>(
    observer: &Position<C, F, U>,
    target: &Position<C, F, U>,
) -> (Direction<F>, Quantity<U>)
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    let displacement: Displacement<F, U> = target - observer;
    let distance = displacement.magnitude();
    let direction = displacement
        .normalize()
        .expect("line_of_sight requires distinct observer and target positions");

    (direction, distance)
}

/// Attempts to compute line-of-sight, returning `None` if positions are identical.
///
/// This is the non-panicking version of [`line_of_sight`].
#[inline]
pub fn try_line_of_sight<C, F, U>(
    observer: &Position<C, F, U>,
    target: &Position<C, F, U>,
) -> Option<Direction<F>>
where
    C: ReferenceCenter,
    F: ReferenceFrame,
    U: LengthUnit,
{
    let displacement: Displacement<F, U> = target - observer;
    displacement.normalize()
}

#[cfg(test)]
mod tests {
    use super::*;
    // Import the derives
    use crate::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};
    use qtty::Meter;

    // Define test-specific frame and center
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct TestFrame;
    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct TestCenter;

    type TestPos = Position<TestCenter, TestFrame, Meter>;

    #[test]
    fn test_line_of_sight_basic() {
        let observer = TestPos::new(0.0, 0.0, 0.0);
        let target = TestPos::new(3.0, 4.0, 0.0);

        let los = line_of_sight(&observer, &target);
        assert!((los.x() - 0.6).abs() < 1e-12);
        assert!((los.y() - 0.8).abs() < 1e-12);
        assert!(los.z().abs() < 1e-12);
    }

    #[test]
    fn test_line_of_sight_with_distance() {
        let observer = TestPos::new(1.0, 1.0, 1.0);
        let target = TestPos::new(4.0, 5.0, 1.0);

        let (dir, dist) = line_of_sight_with_distance(&observer, &target);
        assert!((dist.value() - 5.0).abs() < 1e-12);
        assert!((dir.x() - 0.6).abs() < 1e-12);
        assert!((dir.y() - 0.8).abs() < 1e-12);
    }

    #[test]
    fn test_try_line_of_sight_same_position() {
        let pos = TestPos::new(1.0, 2.0, 3.0);
        assert!(try_line_of_sight(&pos, &pos).is_none());
    }

    #[test]
    fn test_position_displacement_roundtrip() {
        let a = TestPos::new(1.0, 2.0, 3.0);
        let b = TestPos::new(5.0, 7.0, 11.0);

        // a + (b - a) == b
        let displacement = b - a;
        let result = a + displacement;

        assert!((result.x().value() - b.x().value()).abs() < 1e-12);
        assert!((result.y().value() - b.y().value()).abs() < 1e-12);
        assert!((result.z().value() - b.z().value()).abs() < 1e-12);
    }

    #[test]
    fn test_direction_scale_to_displacement() {
        use qtty::Quantity;
        let dir = Direction::<TestFrame>::new(1.0, 0.0, 0.0);
        let disp: Displacement<TestFrame, Meter> = dir * Quantity::new(3.0);

        assert!((disp.x().value() - 3.0).abs() < 1e-12);
        assert!(disp.y().value().abs() < 1e-12);
    }

    #[test]
    fn test_displacement_normalize_to_direction() {
        let disp = Displacement::<TestFrame, Meter>::new(3.0, 4.0, 0.0);
        let dir = disp.normalize().expect("non-zero displacement");

        // Check normalization: 3/5 = 0.6, 4/5 = 0.8
        assert!((dir.x() - 0.6).abs() < 1e-12);
        assert!((dir.y() - 0.8).abs() < 1e-12);
        assert!(dir.z().abs() < 1e-12);
    }
}
