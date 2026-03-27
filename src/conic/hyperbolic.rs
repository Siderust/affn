//! Kind marker for hyperbolic conics.

use super::{sealed, ConicKind, KindMarker, NonParabolicKindMarker};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Marker type for hyperbolic conics (`e > 1`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Hyperbolic;

impl sealed::KindMarkerSealed for Hyperbolic {}

impl KindMarker for Hyperbolic {
    fn conic_kind() -> ConicKind {
        ConicKind::Hyperbolic
    }
}

impl NonParabolicKindMarker for Hyperbolic {}
