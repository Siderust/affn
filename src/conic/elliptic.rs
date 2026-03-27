//! Kind marker for elliptic conics.

use super::{sealed, ConicKind, KindMarker, NonParabolicKindMarker};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Marker type for elliptic conics (`0 <= e < 1`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Elliptic;

impl sealed::KindMarkerSealed for Elliptic {}

impl KindMarker for Elliptic {
    fn conic_kind() -> ConicKind {
        ConicKind::Elliptic
    }
}

impl NonParabolicKindMarker for Elliptic {}
