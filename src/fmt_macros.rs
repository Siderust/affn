//! Internal helpers to factor out the repetitive
//! [`Display`](core::fmt::Display) / [`LowerExp`](core::fmt::LowerExp) /
//! [`UpperExp`](core::fmt::UpperExp) triplet impls used across the coordinate
//! types in this crate.
//!
//! This module is `#[macro_use]`d from `lib.rs` so the macros are available
//! crate-wide. They are intentionally not exported (`#[macro_export]` is *not*
//! used) so they remain a private implementation detail.
//!
//! The single [`impl_quantity_fmt_triplet!`] macro emits the three trait
//! implementations from one declaration. The body is written *once*; the macro
//! supplies a per-impl alias (`use ::core::fmt::Display as $fmt_one;`, etc.)
//! so that the body can dispatch each per-quantity formatting call through the
//! correct trait.
//!
//! ## Shape
//!
//! ```ignore
//! impl_quantity_fmt_triplet! {
//!     impl<C, F, U> for Position<C, F, U>
//!     where { C: ReferenceCenter, F: ReferenceFrame, U: LengthUnit, },
//!     fmt_each: { Quantity<U>, },
//!     |this, f, FmtOne| {
//!         write!(f, "...", ...)?;
//!         FmtOne::fmt(&this.x(), f)?;
//!         // ...
//!     }
//! }
//! ```
//!
//! - `where { ... }` are the *common* bounds shared by all three impls. The
//!   trailing comma is required (it is concatenated with the per-trait bound
//!   list emitted by `fmt_each`).
//! - `fmt_each: { T1, T2, ... }` lists the types whose per-trait bound must be
//!   added to each impl. For an impl of `Display` the macro appends
//!   `T1: ::core::fmt::Display, T2: ::core::fmt::Display, ...`, and likewise for
//!   `LowerExp` and `UpperExp`. Pass an empty list (`fmt_each: {},`) when the
//!   formatted quantities already implement all three traits unconditionally.
//! - The closure-like `|this, f, FmtOne| { body }` captures the names used
//!   inside the body for `&self`, the formatter, and the per-impl trait alias.

macro_rules! impl_quantity_fmt_triplet {
    (
        impl[$($gp:tt)*] for $ty:ty
        where { $($common:tt)* },
        fmt_each: { $($fty:ty),* $(,)? },
        |$self_:ident, $f:ident, $fmt_one:ident| $body:block
    ) => {
        impl<$($gp)*> ::core::fmt::Display for $ty
        where
            $($common)*
            $($fty: ::core::fmt::Display,)*
        {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                #[allow(non_camel_case_types)]
                use ::core::fmt::Display as $fmt_one;
                let $self_ = self;
                let $f = f;
                $body
            }
        }

        impl<$($gp)*> ::core::fmt::LowerExp for $ty
        where
            $($common)*
            $($fty: ::core::fmt::LowerExp,)*
        {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                #[allow(non_camel_case_types)]
                use ::core::fmt::LowerExp as $fmt_one;
                let $self_ = self;
                let $f = f;
                $body
            }
        }

        impl<$($gp)*> ::core::fmt::UpperExp for $ty
        where
            $($common)*
            $($fty: ::core::fmt::UpperExp,)*
        {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                #[allow(non_camel_case_types)]
                use ::core::fmt::UpperExp as $fmt_one;
                let $self_ = self;
                let $f = f;
                $body
            }
        }
    };
}
