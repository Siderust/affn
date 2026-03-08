# affn

[![Crates.io](https://img.shields.io/crates/v/affn.svg)](https://crates.io/crates/affn)
[![Docs](https://docs.rs/affn/badge.svg)](https://docs.rs/affn)
[![Code Quality](https://github.com/Siderust/affn/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Siderust/affn/actions/workflows/ci.yml)


Affine geometry primitives for strongly-typed coordinate systems.

`affn` is a small, domain-agnostic geometry kernel for scientific and engineering software. It provides:

- **Reference centers** (`C`): the origin of a coordinate system (optionally parameterized via `C::Params`)
- **Reference frames** (`F`): the orientation of axes
- **Typed coordinates**: Cartesian, spherical, and ellipsoidal positions plus directions/vectors
- **Affine operators**: `Rotation3`, `Translation3`, and `Isometry3`
- **Units**: distances/lengths are carried via `qtty` units at the type level

The goal is to make invalid operations (like adding two positions) fail at compile time.

## Quick Start

Add the dependency:

```toml
[dependencies]
affn = "0.3"
qtty = "0.4"
```

Define a center + frame and do basic affine algebra:

```rust
use affn::cartesian::{Displacement, Position};
use affn::centers::ReferenceCenter;
use affn::frames::ReferenceFrame;
use qtty::*;

#[derive(Debug, Copy, Clone)]
struct World;
impl ReferenceFrame for World {
    fn frame_name() -> &'static str { "World" }
}

#[derive(Debug, Copy, Clone)]
struct Origin;
impl ReferenceCenter for Origin {
    type Params = ();
    fn center_name() -> &'static str { "Origin" }
}

let a = Position::<Origin, World, Meter>::new(0.0, 0.0, 0.0);
let b = Position::<Origin, World, Meter>::new(3.0, 4.0, 0.0);

// Position - Position -> Displacement
let d: Displacement<World, Meter> = b - a;
assert!((d.magnitude().value() - 5.0).abs() < 1e-12);

// Position + Displacement -> Position
let c = a + d;
assert!((c.y().value() - 4.0).abs() < 1e-12);
```

## Core Concepts

- `Position<C, F, U>`: an affine point (depends on both center and frame)
- `Direction<F>`: a unit vector (frame-only, translation-invariant)
- `Vector<F, U>` / `Displacement<F, U>` / `Velocity<F, U>`: free vectors (frame-only)
- `EllipsoidalPosition<C, F, U>`: geodetic longitude/latitude/height on an ellipsoid-aware frame

The type system enforces the usual affine rules:

- ✅ `Position - Position -> Displacement`
- ✅ `Position + Displacement -> Position`
- ❌ `Position + Position` (does not compile)

## Affine Operators

`affn` includes typed affine operators for pure geometric transforms:

- `Rotation3`
- `Translation3`
- `Isometry3`

These operators preserve the existing frame tag. When you intentionally rotate from one frame into another, retag the result explicitly with `reinterpret_frame`:

```rust
use affn::cartesian::Position;
use affn::ops::Rotation3;
use affn::prelude::*;
use qtty::*;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct FrameA;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct FrameB;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct Center;

let pos_a = Position::<Center, FrameA, Meter>::new(1.0 * M, 0.0 * M, 0.0 * M);
let rot = Rotation3::rz(90.0 * DEG);
let pos_b = (rot * pos_a).reinterpret_frame::<FrameB>();

assert!(pos_b.y().value() > 0.999);
```

## Defining Custom Systems (Derive Macros)

For zero-sized marker types, use the derive macros re-exported by the crate:

```rust
use affn::prelude::*;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct MyFrame;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct MyCenter;
```

Some centers need runtime parameters (e.g. “topocentric” depends on an observer):

```rust
use affn::prelude::*;

#[derive(Clone, Debug, Default, PartialEq)]
struct Observer {
    lat_deg: f64,
    lon_deg: f64,
}

#[derive(Debug, Copy, Clone, ReferenceCenter)]
#[center(params = Observer)]
struct Topocentric;
```

## Spherical ↔ Cartesian

Cartesian and spherical positions can be converted losslessly (up to floating point error):

```rust
use affn::cartesian::Position as CPos;
use affn::spherical::Position as SPos;
use affn::centers::ReferenceCenter;
use affn::frames::ReferenceFrame;
use qtty::*;

#[derive(Debug, Copy, Clone)]
struct Frame;
impl ReferenceFrame for Frame { fn frame_name() -> &'static str { "Frame" } }

#[derive(Debug, Copy, Clone)]
struct Center;
impl ReferenceCenter for Center { type Params = (); fn center_name() -> &'static str { "Center" } }

let cart = CPos::<Center, Frame, Meter>::new(1.0, 1.0, 1.0);
let sph: SPos<Center, Frame, Meter> = cart.to_spherical();
let back: CPos<Center, Frame, Meter> = CPos::from_spherical(&sph);
assert!((back.z().value() - 1.0).abs() < 1e-10);
```

## Ellipsoidal Coordinates

`affn::ellipsoidal::Position<C, F, U>` models geodetic longitude, latitude, and height above an ellipsoid. Conversions to and from Cartesian coordinates are available when the frame implements `HasEllipsoid`.

Built-in terrestrial frames under the `astro` feature already carry ellipsoids:

- `ECEF` uses `Wgs84`
- `ITRF` uses `Grs80`

Example:

```rust
use affn::centers::ReferenceCenter;
use affn::ellipsoidal::Position;
use qtty::*;

#[derive(Debug, Copy, Clone)]
struct Geocentric;
impl ReferenceCenter for Geocentric {
    type Params = ();
    fn center_name() -> &'static str { "Geocentric" }
}

# #[cfg(feature = "astro")]
# {
let geodetic = Position::<Geocentric, affn::frames::ECEF, Meter>::new(
    -17.89 * DEG,
    28.76 * DEG,
    2200.0 * M,
);
let cart = geodetic.to_cartesian::<Meter>();
let roundtrip = Position::<Geocentric, affn::frames::ECEF, Meter>::from_cartesian(&cart);
assert!((roundtrip.height.value() - geodetic.height.value()).abs() < 1e-6);
# }
```

## Built-In Astro Frames (optional)

Enable the `astro` feature to use the built-in astronomy and geodesy marker frames:

```toml
[dependencies]
affn = { version = "0.3", features = ["astro"] }
qtty = "0.4"
```

Available built-ins include:

- Equatorial: `ICRS`, `ICRF`, `EquatorialMeanJ2000`, `EME2000`, `EquatorialMeanOfDate`, `EquatorialTrueOfDate`, `GCRS`, `CIRS`, `TIRS`, `FK4B1950`, `TEME`
- Ecliptic and galactic: `EclipticMeanJ2000`, `EclipticOfDate`, `EclipticTrueOfDate`, `Galactic`
- Terrestrial and horizontal: `Horizontal`, `ECEF`, `ITRF`
- Planetary body-fixed: `MercuryFixed`, `VenusFixed`, `MarsFixed`, `MoonPrincipalAxes`, `JupiterSystemIII`, `SaturnFixed`, `UranusFixed`, `NeptuneFixed`, `PlutoFixed`

## Examples

Run the included examples:

- `cargo run --example basic_cartesian`
- `cargo run --example parameterized_center`
- `cargo run --example spherical_roundtrip`
- `cargo run --example serde_roundtrip --features serde`

## Serde (optional)

`affn` supports `serde` serialization for its core coordinate types behind an opt-in feature flag.

Enable it in your `Cargo.toml`:

```toml
[dependencies]
affn = { version = "0.3", features = ["serde"] }
qtty = "0.4"
```

This feature also forwards serialization support to dependencies where needed (e.g. `qtty/serde`, and nalgebra's `serde-serialize`).

To run the serde example:

- `cargo run --example serde_roundtrip --features serde`

Or to run tests including serde round-trips:

- `cargo test --features serde`

## License

Licensed under `AGPL-3.0-only`. See `LICENSE`.
