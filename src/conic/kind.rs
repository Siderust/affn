#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// High-level conic classification derived from eccentricity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ConicKind {
    /// Elliptic orbit or conic (`0 <= e < 1`).
    Elliptic,
    /// Parabolic orbit or conic (`e == 1`).
    Parabolic,
    /// Hyperbolic orbit or conic (`e > 1`).
    Hyperbolic,
}
