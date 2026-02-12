//! Shared serde utility functions.

/// Returns `true` if `T` is a zero-sized type (for `skip_serializing_if`).
pub(crate) fn is_zero_sized<T>(_: &T) -> bool {
    std::mem::size_of::<T>() == 0
}
