//! Internal macros that forward a by-value operator impl to the three
//! reference variants (`&T op U`, `T op &U`, `&T op &U`).
//!
//! # Cost model
//!
//! These macros implement the reference variants by dereferencing
//! (`*self` / `*rhs`) and delegating to the by-value impl. They therefore
//! require both operand types to be `Copy`. For most affine geometry types
//! in this crate the underlying storage is a small fixed-size array of
//! `f64`/`Quantity<U>`, so the bitwise copy is trivial and the compiler can
//! inline it away.
//!
//! For types whose `Copy`-ness depends on a generic parameter (e.g.
//! `Position<C, F, U>` is `Copy` only when `C::Params: Copy`), callers add
//! the appropriate `where` clause to the macro invocation; the generated
//! impls are then bounded the same way and never apply when the by-value
//! impl is moved-only.
//!
//! Three atomic helpers (`_lhs`, `_rhs`, `_both`) exist so call sites can
//! opt out of generating a particular variant when a hand-written one
//! already exists — emitting it would conflict with the existing impl.

macro_rules! forward_ref_binop_lhs {
    (impl[$($gp:tt)*] $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        impl<$($gp)*> core::ops::$imp<$u> for &$t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp<$u>>::Output;
            #[inline]
            fn $method(self, rhs: $u) -> <Self as core::ops::$imp<$u>>::Output {
                (*self).$method(rhs)
            }
        }
    };
    (impl $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        impl core::ops::$imp<$u> for &$t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp<$u>>::Output;
            #[inline]
            fn $method(self, rhs: $u) -> <Self as core::ops::$imp<$u>>::Output {
                (*self).$method(rhs)
            }
        }
    };
}

macro_rules! forward_ref_binop_rhs {
    (impl[$($gp:tt)*] $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        impl<$($gp)*> core::ops::$imp<&$u> for $t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp<$u>>::Output;
            #[inline]
            fn $method(self, rhs: &$u) -> <Self as core::ops::$imp<&$u>>::Output {
                self.$method(*rhs)
            }
        }
    };
    (impl $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        impl core::ops::$imp<&$u> for $t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp<$u>>::Output;
            #[inline]
            fn $method(self, rhs: &$u) -> <Self as core::ops::$imp<&$u>>::Output {
                self.$method(*rhs)
            }
        }
    };
}

macro_rules! forward_ref_binop_both {
    (impl[$($gp:tt)*] $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        impl<$($gp)*> core::ops::$imp<&$u> for &$t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp<$u>>::Output;
            #[inline]
            fn $method(self, rhs: &$u) -> <Self as core::ops::$imp<&$u>>::Output {
                (*self).$method(*rhs)
            }
        }
    };
    (impl $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        impl core::ops::$imp<&$u> for &$t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp<$u>>::Output;
            #[inline]
            fn $method(self, rhs: &$u) -> <Self as core::ops::$imp<&$u>>::Output {
                (*self).$method(*rhs)
            }
        }
    };
}

/// Generates all three reference variants (`&T op U`, `T op &U`, `&T op &U`)
/// from a by-value impl `T op U`. See module docs for the cost/`Copy` model.
///
/// Generic parameters (when present) are written in brackets: `impl[F, U]` —
/// this avoids local ambiguity from `tt`-greedy matching of `<...>`.
macro_rules! forward_ref_binop {
    (impl[$($gp:tt)*] $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        forward_ref_binop_lhs!  { impl[$($gp)*] $imp, $method for $t, $u $(where ($($wp)*))? }
        forward_ref_binop_rhs!  { impl[$($gp)*] $imp, $method for $t, $u $(where ($($wp)*))? }
        forward_ref_binop_both! { impl[$($gp)*] $imp, $method for $t, $u $(where ($($wp)*))? }
    };
    (impl $imp:ident, $method:ident for $t:ty, $u:ty
     $(where ($($wp:tt)*))?) => {
        forward_ref_binop_lhs!  { impl $imp, $method for $t, $u $(where ($($wp)*))? }
        forward_ref_binop_rhs!  { impl $imp, $method for $t, $u $(where ($($wp)*))? }
        forward_ref_binop_both! { impl $imp, $method for $t, $u $(where ($($wp)*))? }
    };
}

/// Generates the reference variant (`&T -> Out`) for a unary operator impl.
macro_rules! forward_ref_unop {
    (impl[$($gp:tt)*] $imp:ident, $method:ident for $t:ty
     $(where ($($wp:tt)*))?) => {
        impl<$($gp)*> core::ops::$imp for &$t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp>::Output;
            #[inline]
            fn $method(self) -> <Self as core::ops::$imp>::Output {
                (*self).$method()
            }
        }
    };
    (impl $imp:ident, $method:ident for $t:ty
     $(where ($($wp:tt)*))?) => {
        impl core::ops::$imp for &$t
        $(where $($wp)*)?
        {
            type Output = <$t as core::ops::$imp>::Output;
            #[inline]
            fn $method(self) -> <Self as core::ops::$imp>::Output {
                (*self).$method()
            }
        }
    };
}
