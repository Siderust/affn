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
//! Use the provided macros to define domain-specific marker types:
//!
//! ```rust,ignore
//! // From external crate:
//! affn::new_frame!(MyLocalFrame);
//! affn::new_center!(MyOrigin);
//! ```
//!
//! Or implement the traits manually:
//!
//! ```rust
//! use affn::frames::ReferenceFrame;
//! use affn::centers::ReferenceCenter;
//!
//! #[derive(Debug, Copy, Clone)]
//! struct MyFrame;
//! impl ReferenceFrame for MyFrame {
//!     fn frame_name() -> &'static str { "MyFrame" }
//! }
//!
//! #[derive(Debug, Copy, Clone)]
//! struct MyOrigin;
//! impl ReferenceCenter for MyOrigin {
//!     type Params = ();
//!     fn center_name() -> &'static str { "MyOrigin" }
//! }
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

// Coordinate type implementations
pub mod cartesian;
pub mod spherical;

// Core traits and marker types
pub mod centers;
pub mod frames;

// Re-export commonly used traits at crate level
pub use centers::{AffineCenter, NoCenter, ReferenceCenter};
pub use frames::ReferenceFrame;

// Re-export concrete Position/Direction types for standalone usage
pub use cartesian::{Direction as CartesianDirection, Displacement, Position, Velocity, Vector};
pub use spherical::{Direction as SphericalDirection, Position as SphericalPosition};
