//! # affn - Affine Geometry Primitives
//!
//! This crate provides strongly-typed coordinate systems with compile-time safety for
//! scientific computing applications. It defines the mathematical foundation for
//! working with positions, directions, and displacements in various reference frames.
//!
//! ## Domain-Agnostic Design
//!
//! `affn` is a **pure geometry kernel** that contains no domain-specific vocabulary.
//! Concrete frame and center types (e.g., astronomical frames, robotic frames)
//! should be defined in downstream crates that depend on `affn`.
//! See [`conic`] for the dedicated guide to the conic geometry layer.
//!
//! ## Core Concepts
//!
//! ### Reference Centers
//!
//! A [`ReferenceCenter`] defines the origin point of a coordinate system.
//! Some centers require runtime parameters (stored in `ReferenceCenter::Params`).
//!
//! ### Reference Frames
//!
//! A [`ReferenceFrame`] defines the orientation of coordinate axes.
//!
//! ### Coordinate Types
//!
//! - **Position**: An affine point in space (center + frame + distance)
//! - **Direction**: A unit vector representing orientation (frame only)
//! - **Displacement/Velocity**: Free vectors (frame + magnitude)
//! - **Conic geometry**: Reusable conic-family classification plus shape and
//!   orientation containers without time or propagation semantics
//!
//! ## Creating Custom Frames and Centers
//!
//! Use derive macros for convenient definitions:
//!
//! ```rust
//! use affn::prelude::*;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct MyFrame;
//!
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct MyCenter;
//!
//! assert_eq!(MyFrame::frame_name(), "MyFrame");
//! assert_eq!(MyCenter::center_name(), "MyCenter");
//! ```
//!
//! Typos in derive attributes are compile errors:
//!
//! ```compile_fail
//! use affn::prelude::*;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! #[frame(azimth = "Equatorial")] // typo: should be "name"
//! struct BadFrame;
//! ```
//!
//! ```compile_fail
//! use affn::prelude::*;
//!
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! #[center(nme = "Earth")] // typo: should be "name"
//! struct BadCenter;
//! ```
//!
//! ## Algebraic Rules
//!
//! The type system enforces mathematical correctness:
//!
//! | Operation | Result | Meaning |
//! |-----------|--------|---------|
//! | `Position - Position` | `Displacement` | Displacement between points |
//! | `Position + Displacement` | `Position` | Translate point |
//! | `Displacement + Displacement` | `Displacement` | Add displacements |
//! | `Direction * Length` | `Displacement` | Scale direction |
//! | `normalize(Displacement)` | `Direction` | Extract orientation |
//!
//! ## Example
//!
//! ```rust
//! use affn::cartesian::{Position, Displacement};
//! use affn::frames::ReferenceFrame;
//! use affn::centers::ReferenceCenter;
//! use affn::qtty::units::Kilometer;
//!
//! // Define domain-specific types
//! #[derive(Debug, Copy, Clone)]
//! struct WorldFrame;
//! impl ReferenceFrame for WorldFrame {
//!     fn frame_name() -> &'static str { "WorldFrame" }
//! }
//!
//! #[derive(Debug, Copy, Clone)]
//! struct WorldOrigin;
//! impl ReferenceCenter for WorldOrigin {
//!     type Params = ();
//!     fn center_name() -> &'static str { "WorldOrigin" }
//! }
//!
//! let a = Position::<WorldOrigin, WorldFrame, Kilometer>::new(100.0, 200.0, 300.0);
//! let b = Position::<WorldOrigin, WorldFrame, Kilometer>::new(150.0, 250.0, 350.0);
//!
//! // Positions subtract to give displacements
//! let displacement: Displacement<WorldFrame, Kilometer> = b - a;
//! ```
//!
//! ## Units via `qtty`
//!
//! Lengths, angles, and related quantities in `affn`'s public API use
//! [`qtty`](https://docs.rs/qtty) types. Prefer the re-exported
//! [`affn::qtty`](crate::qtty) path so you always get the same `qtty`
//! instance that `affn` was compiled against:
//!
//! ```rust
//! use affn::qtty::units::Meter;
//! use affn::qtty::{Quantity, M};
//! ```
//!
//! Re-exporting does **not** force Cargo to unify incompatible `qtty`
//! versions if another crate depends on a semver-incompatible release;
//! crates that exchange `qtty` values should still agree on compatible
//! dependency ranges. An incompatible `qtty` upgrade is treated as a
//! potentially breaking change for `affn`.
//!
//! ## `no_std` support
//!
//! `affn` is `no_std`-compatible. Feature flags:
//!
//! - **`std`** (default): enables the Rust standard library and implies `alloc`.
//! - **`alloc`**: enables heap-backed APIs such as [`interpolation`] and
//!   `serde` helpers that need `String`.
//! - **neither**: pure `core`-only geometry (no heap).
//!
//! ```toml
//! # Default (std)
//! affn = "0.10"
//!
//! # no_std with heap
//! affn = { version = "0.10", default-features = false, features = ["alloc"] }
//!
//! # pure no_std (core only)
//! affn = { version = "0.10", default-features = false }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// Allow the crate to refer to itself as `::affn::` for derive macro compatibility
extern crate self as affn;

// Internal `Display`/`LowerExp`/`UpperExp` triplet macro. Must precede any
// modules that use it.
#[macro_use]
mod fmt_macros;

#[macro_use]
mod op_macros;

// Coordinate type implementations
pub mod cartesian;
pub mod conic;
#[cfg(feature = "alloc")]
pub mod interpolation;
pub mod spherical;

// Core traits and marker types
pub mod centers;
pub mod frames;

// Ellipsoid definitions and frame-ellipsoid association
pub mod ellipsoid;

// Ellipsoidal coordinate system (lon, lat, height-above-ellipsoid)
pub mod ellipsoidal;

// Affine operators (rotation, translation, isometry)
pub mod algebra;
pub mod ops;
pub mod planar;

// Typed inter-reference-system transforms (not re-exported at crate root /
// prelude to avoid colliding with domain crates that define their own
// `Transform` traits — e.g. siderust).
pub mod transform;

// Shared serde utilities
#[cfg(feature = "serde")]
pub(crate) mod serde_utils;

// Frame-tagged 3×3 matrix primitives
pub mod matrix3;

// Frame-tagged 6×6 matrix and block-diagonal rotation helper
pub mod matrix6;

// Re-export derive macros from affn-derive
// Named with Derive prefix to avoid conflicts with trait names
pub use affn_derive::{
    ReferenceCenter as DeriveReferenceCenter, ReferenceFrame as DeriveReferenceFrame,
};

/// Re-export of the [`qtty`] crate used by `affn`'s public API.
///
/// Prefer `affn::qtty` over a separate direct `qtty` dependency when
/// constructing quantities for `affn` types, so values share the same
/// crate instance that `affn` was compiled against.
///
/// This re-export does not prevent Cargo from resolving a second,
/// semver-incompatible `qtty` if another crate depends on one explicitly.
pub use qtty;

// Re-export traits at crate level with their original names
// This is the standard pattern: traits and derives co-exist with same names
pub use centers::{AffineCenter, NoCenter, ReferenceCenter};
pub use frames::ReferenceFrame;

// Re-export operators at crate level
pub use ops::{Isometry3, Rotation3, Translation3};

// Re-export concrete Position/Direction types for standalone usage
pub use cartesian::{
    Acceleration, CenterParamsMismatchError, Direction as CartesianDirection, Displacement, Force,
    Position, Vector, Velocity,
};
pub use conic::{
    ClassifiedPeriapsisParam, ClassifiedSemiMajorAxisParam, ConicKind, ConicOrientation,
    ConicShape, ConicValidationError, Elliptic, EllipticPeriapsis, EllipticSemiMajorAxis,
    Hyperbolic, HyperbolicPeriapsis, HyperbolicSemiMajorAxis, KindMarker, NonParabolicKindMarker,
    OrientedConic, Parabolic, ParabolicPeriapsis, PeriapsisParam, SemiMajorAxisParam,
    TypedPeriapsisParam, TypedSemiMajorAxisParam,
};
pub use spherical::{Direction as SphericalDirection, Position as SphericalPosition};

// Re-export ellipsoidal Position for standalone usage
pub use ellipsoidal::{GeodeticConvergenceError, Position as EllipsoidalPosition};

/// Prelude module for convenient imports.
///
/// Import everything you need with:
/// ```rust
/// use affn::prelude::*;
/// ```
pub mod prelude {
    // Derive macros - aliased to standard names in prelude
    pub use crate::{
        DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame,
    };

    // Traits - keep full names to avoid conflicts with derives
    pub use crate::centers::{AffineCenter, NoCenter, ReferenceCenter as ReferenceCenterTrait};
    pub use crate::frames::ReferenceFrame as ReferenceFrameTrait;

    // Core coordinate types
    pub use crate::cartesian::{
        Acceleration, Direction as CartesianDirection, Displacement, Force, Position, Vector,
        Velocity,
    };
    pub use crate::conic::{
        ClassifiedPeriapsisParam, ClassifiedSemiMajorAxisParam, ConicKind, ConicOrientation,
        ConicShape, ConicValidationError, Elliptic, EllipticPeriapsis, EllipticSemiMajorAxis,
        Hyperbolic, HyperbolicPeriapsis, HyperbolicSemiMajorAxis, KindMarker,
        NonParabolicKindMarker, OrientedConic, Parabolic, ParabolicPeriapsis, PeriapsisParam,
        SemiMajorAxisParam, TypedPeriapsisParam, TypedSemiMajorAxisParam,
    };
    #[cfg(feature = "alloc")]
    pub use crate::interpolation::{
        CubicHermiteTable, HermiteInterpolable, HermiteNode, HermiteTableEvaluation,
        InterpolationAbscissa, InterpolationError, ScalarCubicHermiteTable, ScalarHermiteNode,
        ScalarHermiteTableEvaluation,
    };
    pub use crate::spherical::{Direction as SphericalDirection, Position as SphericalPosition};

    // Operators
    pub use crate::ops::{Isometry3, Rotation3, Translation3};

    // Ellipsoidal coordinate type (always available)
    pub use crate::ellipsoidal::{GeodeticConvergenceError, Position as EllipsoidalPosition};

    // Ellipsoid traits and predefined ellipsoids (always available)
    pub use crate::ellipsoid::{Ellipsoid, Grs80, HasEllipsoid, Iers2003, Wgs84};

    // Feature-gated astronomical frames
    #[cfg(feature = "astro")]
    pub use crate::frames::{
        EclipticMeanJ2000, EclipticMeanOfDate, EclipticOfDate, EclipticTrueOfDate,
        EquatorialMeanJ2000, EquatorialMeanOfDate, EquatorialTrueOfDate, Galactic, Horizontal,
        ECEF, ICRF, ICRS, ITRF,
    };
}
