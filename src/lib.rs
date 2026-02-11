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
//!
//! ## Core Concepts
//!
//! ### Reference Centers
//!
//! A [`ReferenceCenter`](centers::ReferenceCenter) defines the origin point of a coordinate system.
//! Some centers require runtime parameters (stored in `ReferenceCenter::Params`).
//!
//! ### Reference Frames
//!
//! A [`ReferenceFrame`](frames::ReferenceFrame) defines the orientation of coordinate axes.
//!
//! ### Coordinate Types
//!
//! - **Position**: An affine point in space (center + frame + distance)
//! - **Direction**: A unit vector representing orientation (frame only)
//! - **Displacement/Velocity**: Free vectors (frame + magnitude)
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
//! use qtty::*;
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

// Allow the crate to refer to itself as `::affn::` for derive macro compatibility
extern crate self as affn;

// Coordinate type implementations
pub mod cartesian;
pub mod spherical;

// Core traits and marker types
pub mod centers;
pub mod frames;

// Affine operators (rotation, translation, isometry)
pub mod ops;

// Re-export derive macros from affn-derive
// Named with Derive prefix to avoid conflicts with trait names
pub use affn_derive::{
    ReferenceCenter as DeriveReferenceCenter, ReferenceFrame as DeriveReferenceFrame,
};

// Re-export traits at crate level with their original names
// This is the standard pattern: traits and derives co-exist with same names
pub use centers::{AffineCenter, NoCenter, ReferenceCenter};
pub use frames::ReferenceFrame;

// Re-export operators at crate level
pub use ops::{Isometry3, Rotation3, Translation3};

// Re-export concrete Position/Direction types for standalone usage
pub use cartesian::{Direction as CartesianDirection, Displacement, Position, Vector, Velocity};
pub use spherical::{Direction as SphericalDirection, Position as SphericalPosition};

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
        Direction as CartesianDirection, Displacement, Position, Vector, Velocity,
    };
    pub use crate::spherical::{Direction as SphericalDirection, Position as SphericalPosition};

    // Operators
    pub use crate::ops::{Isometry3, Rotation3, Translation3};

    // Feature-gated astronomical frames
    #[cfg(feature = "astro")]
    pub use crate::frames::{
        ECEF, Ecliptic, EquatorialMeanJ2000, EquatorialMeanOfDate, EquatorialTrueOfDate, Galactic,
        Horizontal, ICRS, ITRF,
    };
}
