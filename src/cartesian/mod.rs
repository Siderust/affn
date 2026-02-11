//! # Cartesian Coordinates Module
//!
//! This module provides strongly-typed Cartesian coordinate types for
//! calculations, with mathematical correctness enforced through the type system.
//!
//! ## Mathematical Model
//!
//! The module implements a rigorous distinction between three fundamentally
//! different mathematical objects:
//!
//! ### [`Direction<F>`] — Unit Vector (Orientation)
//!
//! A dimensionless unit vector representing pure orientation in space.
//!
//! - **Frame-dependent**: Orientation is relative to frame `F`
//! - **Center-independent**: Directions are translation-invariant
//! - **Dimensionless**: Magnitude is always 1
//! - **Valid operations**: Rotation (frame transform), dot/cross products
//!
//! ### [`Displacement<F, U>`] — Free Displacement Vector
//!
//! A free vector representing directed magnitude (displacement) in space.
//!
//! - **Frame-dependent**: Direction is relative to frame `F`
//! - **Center-independent**: Displacements are translation-invariant
//! - **Dimensioned**: Has length unit `U`
//! - **Valid operations**: Addition, subtraction, scaling, normalization
//!
//! ### [`Position<C, F, U>`] — Affine Point
//!
//! A point in affine space, representing a location relative to an origin.
//!
//! - **Center-dependent**: Position is measured from center `C`
//! - **Frame-dependent**: Coordinates are relative to frame `F`
//! - **Dimensioned**: Has length unit `U`
//! - **Valid operations**: Subtraction (yields Displacement), translation by Displacement
//!
//! ## Algebraic Rules
//!
//! The type system enforces these mathematical constraints:
//!
//! | Operation | Result | Meaning |
//! |-----------|--------|---------|
//! | `Position - Position` | `Displacement` | Displacement between points |
//! | `Position + Displacement` | `Position` | Translate point |
//! | `Displacement + Displacement` | `Displacement` | Add displacements |
//! | `Direction * Length` | `Displacement` | Scale direction |
//! | `normalize(Displacement)` | `Direction` | Extract orientation |
//!
//! ## Forbidden Operations (compile errors)
//!
//! - `Position + Position` — Adding points has no meaning
//! - `Direction + anything` — Unit vectors aren't additive
//! - Center transform on `Direction` — Directions have no center
//!
//! ## Line of Sight
//!
//! To compute the direction from an observer to a target, use [`line_of_sight`]:
//!
//! ```rust
//! use affn::cartesian::{line_of_sight, Position};
//! use affn::frames::ReferenceFrame;
//! use affn::centers::ReferenceCenter;
//! use qtty::*;
//!
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
//! let observer = Position::<WorldOrigin, WorldFrame, Meter>::new(0.0, 0.0, 0.0);
//! let target = Position::<WorldOrigin, WorldFrame, Meter>::new(1.0, 1.0, 0.0);
//!
//! let direction = line_of_sight(&observer, &target);
//! ```
//!
//! ## Architecture
//!
//! All types share a common internal storage [`XYZ<T>`](xyz::XYZ) that implements
//! component-wise operations once. The semantic types are thin wrappers with
//! `PhantomData` markers for type safety. This provides:
//!
//! - **Zero-cost abstractions**: `#[repr(transparent)]` where applicable
//! - **No code duplication**: Math is centralized in `XYZ<T>`
//! - **Type safety**: Invalid operations are compile errors

// Internal shared storage (pub(crate) for use by ops module)
pub(crate) mod xyz;

// Semantic types
mod direction;
mod line_of_sight;
mod position; // Position<C, F, U> - Affine point
mod vector; // Vector<F, U> - Free vector (base for Displacement, Velocity) // Direction<F> - Unit vector

// =============================================================================
// Public Re-exports
// =============================================================================

// Re-export XYZ for internal crate use
pub use xyz::XYZ;

pub use direction::Direction;
pub use position::Position;
pub use vector::{Displacement, Vector, Velocity};

pub use line_of_sight::{line_of_sight, line_of_sight_with_distance, try_line_of_sight};
