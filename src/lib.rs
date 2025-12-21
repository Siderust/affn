//! # affn - Affine Geometry Primitives
//!
//! This crate provides strongly-typed coordinate systems with compile-time safety for
//! scientific computing applications. It defines the mathematical foundation for
//! working with positions, directions, and displacements in various reference frames.
//!
//! ## Core Concepts
//!
//! ### Reference Centers
//!
//! A [`ReferenceCenter`](centers::ReferenceCenter) defines the origin point of a coordinate system.
//! Some centers require runtime parameters (like observer location for topocentric coordinates).
//!
//! ### Reference Frames
//!
//! A [`ReferenceFrame`](frames::ReferenceFrame) defines the orientation of coordinate axes.
//! Common frames include ICRS, Ecliptic, Equatorial, and Horizontal.
//!
//! ### Coordinate Types
//!
//! - **Position**: An affine point in space (center + frame + distance)
//! - **Direction**: A unit vector representing orientation (frame only)
//! - **Displacement/Velocity**: Free vectors (frame + magnitude)
//!
//! ## Usage Modes
//!
//! This crate can be used in two ways:
//!
//! 1. **Standalone**: Use the provided `cartesian` and `spherical` modules directly
//!    for complete coordinate type implementations.
//!
//! 2. **Framework**: Import only the traits (`ReferenceFrame`, `ReferenceCenter`, etc.)
//!    and marker types (ICRS, Ecliptic, Heliocentric, etc.) to build your own
//!    coordinate types with custom transformations.
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
//! ## Example (Standalone Mode)
//!
//! ```rust
//! use affn::cartesian::{Position, Displacement};
//! use affn::centers::Geocentric;
//! use affn::frames::ICRS;
//! use qtty::*;
//!
//! let a = Position::<Geocentric, ICRS, Kilometer>::new(100.0, 200.0, 300.0);
//! let b = Position::<Geocentric, ICRS, Kilometer>::new(150.0, 250.0, 350.0);
//!
//! // Positions subtract to give displacements
//! let displacement: Displacement<ICRS, Kilometer> = b - a;
//! ```

// Coordinate type implementations
pub mod cartesian;
pub mod spherical;

// Core traits and marker types
pub mod centers;
pub mod frames;

// Re-export commonly used traits at crate level
pub use centers::{AffineCenter, NoCenter, ObserverSite, ReferenceCenter};
pub use frames::ReferenceFrame;

// Re-export concrete Position/Direction types for standalone usage
pub use cartesian::{Direction as CartesianDirection, Displacement, Position, Velocity, Vector};
pub use spherical::{Direction as SphericalDirection, Position as SphericalPosition};
