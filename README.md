# affn

Affine geometry primitives for strongly-typed coordinate systems.

`affn` is a small, domain-agnostic geometry kernel for scientific/engineering software. It provides:

- **Reference centers** (`C`): the origin of a coordinate system (optionally parameterized via `C::Params`)
- **Reference frames** (`F`): the orientation of axes
- **Typed coordinates**: Cartesian and spherical positions and directions
- **Units**: distances/lengths are carried via `qtty` units at the type level

The goal is to make invalid operations (like adding two positions) fail at compile time.

## Quick Start

Add the dependency:

```toml
[dependencies]
affn = "0.1"
qtty = "0.2"
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

The type system enforces the usual affine rules:

- ✅ `Position - Position -> Displacement`
- ✅ `Position + Displacement -> Position`
- ❌ `Position + Position` (does not compile)

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

## Examples

Run the included examples:

- `cargo run --example basic_cartesian`
- `cargo run --example parameterized_center`
- `cargo run --example spherical_roundtrip`

## Publishing Notes

`affn` re-exports proc-macros from the companion crate `affn-derive`. If publishing to crates.io,
publish `affn-derive` first (same version), then publish `affn`.

## License

Licensed under `AGPL-3.0-only`. See `LICENSE`.
