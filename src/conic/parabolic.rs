use super::{sealed, ConicKind, KindMarker};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Marker type for parabolic conics (`e == 1`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Parabolic;

impl sealed::KindMarkerSealed for Parabolic {}

impl KindMarker for Parabolic {
    fn conic_kind() -> ConicKind {
        ConicKind::Parabolic
    }
}
