//! # Reference Frames Module
//!
//! This module defines the concept of a *reference frame* for coordinate systems.
//! A reference frame specifies the orientation of the axes used to describe positions in space.
//!
//! ## Overview
//!
//! The [`ReferenceFrame`] trait provides a common interface for all reference frame types.
//! Each frame is represented as a zero-sized struct and implements the trait to provide
//! its canonical name.
//!
//! ## Domain-Agnostic Design
//!
//! This module provides **only** the trait infrastructure. Concrete frame types
//! (e.g., astronomical frames, geographic frames, robotic frames) should be defined
//! in domain-specific crates that depend on `affn`.
//!
//! ## Creating Custom Frames
//!
//! Use the [`new_frame!`] macro to define frame marker types:
//!
//! ```rust,ignore
//! // From external crate:
//! affn::new_frame!(MyCustomFrame);
//! ```
//!
//! Or implement the trait manually:
//!
//! ```rust
//! use affn::frames::ReferenceFrame;
//!
//! #[derive(Debug, Copy, Clone)]
//! pub struct MyFrame;
//!
//! impl ReferenceFrame for MyFrame {
//!     fn frame_name() -> &'static str {
//!         "MyFrame"
//!     }
//! }
//! assert_eq!(MyFrame::frame_name(), "MyFrame");
//! ```

/// A trait for defining a reference frame (orientation).
///
/// Reference frames define the orientation of coordinate axes. Different frames
/// represent different ways of orienting a coordinate system (e.g., aligned with
/// an equator, an orbital plane, a horizon, etc.).
///
/// # Implementing
///
/// Implement this trait for zero-sized marker types that represent different frames:
///
/// ```rust
/// use affn::frames::ReferenceFrame;
///
/// #[derive(Debug, Copy, Clone)]
/// pub struct MyFrame;
///
/// impl ReferenceFrame for MyFrame {
///     fn frame_name() -> &'static str {
///         "MyFrame"
///     }
/// }
/// ```
pub trait ReferenceFrame: Copy + Clone + std::fmt::Debug {
    /// Returns the canonical name of this reference frame.
    fn frame_name() -> &'static str;
}

/// Macro to conveniently declare new reference frame types.
///
/// This creates a zero-sized struct that implements [`ReferenceFrame`].
///
/// # Example
///
/// ```rust,ignore
/// // From external crate:
/// affn::new_frame!(LocalFrame);
/// assert_eq!(LocalFrame::frame_name(), "LocalFrame");
/// ```
#[macro_export]
macro_rules! new_frame {
    ($name:ident) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
        pub struct $name;

        impl $crate::frames::ReferenceFrame for $name {
            fn frame_name() -> &'static str {
                stringify!($name)
            }
        }
    };
}
