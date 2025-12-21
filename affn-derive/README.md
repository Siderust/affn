# affn-derive

Procedural macros for the [affn](https://crates.io/crates/affn) crate, providing convenient derive macros for `ReferenceFrame` and `ReferenceCenter` traits.

## Overview

This crate provides derive macros that automatically implement the `ReferenceFrame` and `ReferenceCenter` traits from the `affn` crate, eliminating boilerplate and providing better IDE support than declarative macros.

## Usage

These derives are re-exported from the `affn` crate, so you typically don't need to depend on this crate directly:

```rust
use affn::prelude::*;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct MyFrame;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct MyCenter;

assert_eq!(MyFrame::frame_name(), "MyFrame");
assert_eq!(MyCenter::center_name(), "MyCenter");
```

## Attributes

### `#[derive(ReferenceFrame)]`

Implements the `ReferenceFrame` trait with the struct name as the frame name.

**Optional attributes:**
- `#[frame(name = "CustomName")]` - Override the frame name

**Example:**
```rust
use affn::prelude::*;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
#[frame(name = "International Celestial Reference System")]
struct ICRS;

assert_eq!(ICRS::frame_name(), "International Celestial Reference System");
```

### `#[derive(ReferenceCenter)]`

Implements the `ReferenceCenter` trait with `Params = ()` by default. Also automatically implements the `AffineCenter` marker trait.

**Optional attributes:**
- `#[center(name = "CustomName")]` - Override the center name
- `#[center(params = MyType)]` - Specify a custom `Params` type (must implement `Clone + Debug + Default + PartialEq`)
- `#[center(affine = false)]` - Skip implementing the `AffineCenter` marker trait

**Example (simple center):**
```rust
use affn::prelude::*;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct Heliocentric;

assert_eq!(Heliocentric::center_name(), "Heliocentric");
```

**Example (parameterized center):**
```rust
use affn::prelude::*;

#[derive(Clone, Debug, Default, PartialEq)]
struct ObserverLocation {
    latitude: f64,
    longitude: f64,
    altitude: f64,
}

#[derive(Debug, Copy, Clone, ReferenceCenter)]
#[center(params = ObserverLocation)]
struct Topocentric;
```

## Requirements

The types deriving these traits must also derive or implement:
- `Debug`
- `Copy`
- `Clone`

For parameterized centers, the `Params` type must implement:
- `Clone`
- `Debug`
- `Default`
- `PartialEq`

## Migration from Declarative Macros

If you're migrating from the old `new_frame!` and `new_center!` macros:

**Old:**
```rust
affn::new_frame!(ICRS);
affn::new_center!(Heliocentric);
```

**New:**
```rust
use affn::prelude::*;

#[derive(Debug, Copy, Clone, ReferenceFrame)]
struct ICRS;

#[derive(Debug, Copy, Clone, ReferenceCenter)]
struct Heliocentric;
```

The derive macros provide:
- Better IDE support (autocomplete, go-to-definition, etc.)
- More flexible customization via attributes
- Clearer error messages
- Standard Rust derive syntax

## License

AGPL-3.0-only
