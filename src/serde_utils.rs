//! Shared serde utility functions.
//!
//! These helpers consolidate the boilerplate that appears in every
//! `*_serde.rs` module across the crate: per-field duplicate guards,
//! missing-field unwrapping, and unknown-field skipping inside hand-written
//! `Visitor::visit_map` bodies. They also expose [`is_zero_sized`] for the
//! `center_params` skip-serialize logic shared by all coordinate types.
//!
//! The helpers are `pub(crate)` only — they are an internal implementation
//! detail and not part of the public API.

use serde::de::{self, MapAccess};
use serde::Deserialize;

/// Returns `true` if `T` is a zero-sized type (for `skip_serializing_if`).
pub(crate) fn is_zero_sized<T>(_: &T) -> bool {
    std::mem::size_of::<T>() == 0
}

/// Deserialize the next value from `map` and store it in `slot`, erroring
/// with `duplicate_field(name)` if `slot` was already populated.
pub(crate) fn collect_field<'de, T, M>(
    slot: &mut Option<T>,
    name: &'static str,
    map: &mut M,
) -> Result<(), M::Error>
where
    T: Deserialize<'de>,
    M: MapAccess<'de>,
{
    if slot.is_some() {
        return Err(de::Error::duplicate_field(name));
    }
    *slot = Some(map.next_value()?);
    Ok(())
}

/// Unwrap a required field collected via [`collect_field`], producing a
/// `missing_field(name)` error when the field was never seen.
pub(crate) fn take_required<T, E>(slot: Option<T>, name: &'static str) -> Result<T, E>
where
    E: de::Error,
{
    slot.ok_or_else(|| E::missing_field(name))
}

/// Consume and discard the next value — the canonical "ignore unknown
/// field" branch of `visit_map`.
pub(crate) fn skip_unknown<'de, M>(map: &mut M) -> Result<(), M::Error>
where
    M: MapAccess<'de>,
{
    let _ = map.next_value::<de::IgnoredAny>()?;
    Ok(())
}
