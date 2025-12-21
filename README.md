# affn

**Affine geometry primitives for strongly-typed coordinate systems.**

`affn` provides the mathematical foundation for working with coordinate systems in scientific computing:

- **Reference Centers**: Origin points for coordinate systems (e.g., Heliocentric, Geocentric, Topocentric)
- **Reference Frames**: Orientation of coordinate axes (e.g., ICRS, Ecliptic, Equatorial)
- **Cartesian Types**: Position (affine points), Direction (unit vectors), Displacement/Velocity (free vectors)
- **Spherical Types**: Position and Direction in spherical coordinates

## Features

- **Type Safety**: Compile-time enforcement of coordinate system compatibility
- **Zero-Cost Abstractions**: Thin wrappers with no runtime overhead
- **Mathematical Rigor**: Clear distinction between positions (affine points) and vectors

## Example

```rust
use affn::cartesian::{Position, Direction, Displacement};
use affn::centers::Heliocentric;
use affn::frames::Ecliptic;
use qtty::*;

// Create positions in heliocentric ecliptic coordinates
let earth = Position::<Heliocentric, Ecliptic, AstronomicalUnit>::new(1.0, 0.0, 0.0);
let mars = Position::<Heliocentric, Ecliptic, AstronomicalUnit>::new(1.5, 0.0, 0.0);

// Compute displacement (Position - Position -> Displacement)
let displacement: Displacement<Ecliptic, AstronomicalUnit> = mars - earth;

// Get the direction to Mars
let direction = displacement.normalize().expect("non-zero");
```

## License

AGPL-3.0-only
