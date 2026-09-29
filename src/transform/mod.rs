//! # Typed inter-reference-system transforms
//!
//! This module wraps the pure affine operators in [`crate::ops`] with
//! compile-time source and destination reference-system tags:
//!
//! ```text
//! Transform<FromCenter, FromFrame, ToCenter, ToFrame, Op>
//! ```
//!
//! where `Op` is typically [`Rotation3`], [`Translation3`], or [`Isometry3`].
//!
//! ## Why this exists
//!
//! Bare operators intentionally preserve `Position` center/frame tags; callers
//! re-tag after the fact. That is correct for low-level math, but it cannot
//! enforce that an `A → B` transform is only applied to an `A` source, nor that
//! `A → B` composes only with `B → C`.
//!
//! [`Transform`] encodes those relationships in the type system so that:
//!
//! - application requires a matching source center/frame;
//! - the result is tagged with the destination center/frame;
//! - compatible transforms compose (`A → B` then `B → C` ⇒ `A → C`);
//! - incompatible compositions fail to compile.
//!
//! The module is domain-agnostic. Downstream crates decide *which* rotation or
//! translation is required (epochs, models, ephemerides, …); `affn` only
//! represents and safely composes *how* two reference systems relate.
//!
//! ## Valid operator shapes
//!
//! | Operator | Meaning | Transform shape |
//! |----------|---------|-----------------|
//! | [`Rotation3`] | Frame-only (same center) | `Transform<C, F1, C, F2, Rotation3>` |
//! | [`Translation3`] | Center-only (same frame) | `Transform<C1, F, C2, F, Translation3<U>>` |
//! | [`Isometry3`] | Center and frame | `Transform<C1, F1, C2, F2, Isometry3<U>>` |
//!
//! Only these shapes can be constructed via [`Transform::new`]. Invalid
//! combinations (for example `Rotation3` with different source and destination
//! centers) are rejected at compile time.
//!
//! Center-changing transforms require [`AffineCenter`] on both endpoints
//! (centers marked `#[center(affine = false)]` cannot be used).
//!
//! ## Parameterized centers
//!
//! [`ReferenceCenter::Params`] may be non-trivial. Producing a
//! `Position<ToCenter, …>` requires knowing `ToCenter::Params`.
//!
//! **MVP limitation:** center-changing transforms
//! ([`Translation3`] / [`Isometry3`]) require `Params = ()` on both centers.
//! Frame-only transforms ([`Rotation3`]) preserve `center_params` and work
//! with any [`ReferenceCenter`], including parameterized centers.
//!
//! ## Example
//!
//! ```rust
//! use affn::cartesian::Position;
//! use affn::ops::{Rotation3, Translation3};
//! use affn::prelude::*;
//! use affn::transform::Transform;
//! use qtty::angular::Radians;
//! use qtty::units::Meter;
//! use std::f64::consts::FRAC_PI_2;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FrameA;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FrameB;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct CenterA;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct CenterB;
//!
//! // Frame-only: CenterA stays CenterA; FrameA → FrameB.
//! let frame_tf = Transform::<CenterA, FrameA, CenterA, FrameB, Rotation3>::new(
//!     Rotation3::rz(Radians::new(FRAC_PI_2)),
//! );
//!
//! // Center-only: FrameA stays FrameA; CenterA → CenterB.
//! let center_tf =
//!     Transform::<CenterA, FrameA, CenterB, FrameA, Translation3<Meter>>::new(
//!         Translation3::new(1.0, 0.0, 0.0),
//!     );
//!
//! let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 0.0, 0.0);
//! let after_frame: Position<CenterA, FrameB, Meter> = frame_tf.apply(pos);
//! assert!((after_frame.x().value()).abs() < 1e-12);
//! assert!((after_frame.y().value() - 1.0).abs() < 1e-12);
//!
//! let after_center: Position<CenterB, FrameA, Meter> = center_tf.apply(pos);
//! assert!((after_center.x().value() - 2.0).abs() < 1e-12);
//! ```
//!
//! Invalid source tags fail to compile:
//!
//! ```compile_fail
//! use affn::cartesian::Position;
//! use affn::ops::Rotation3;
//! use affn::prelude::*;
//! use affn::transform::Transform;
//! use qtty::units::Meter;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FrameA;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FrameB;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FrameC;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct Origin;
//!
//! let tf = Transform::<Origin, FrameA, Origin, FrameB, Rotation3>::new(
//!     Rotation3::IDENTITY,
//! );
//! let wrong = Position::<Origin, FrameC, Meter>::new(1.0, 0.0, 0.0);
//! // FrameC is not FrameA — this must not compile:
//! let _ = tf.apply(wrong);
//! ```
//!
//! `Rotation3` cannot be constructed with different source and destination centers:
//!
//! ```compile_fail
//! use affn::ops::Rotation3;
//! use affn::prelude::*;
//! use affn::transform::Transform;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct F1;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct F2;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct A;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct B;
//!
//! let _ = Transform::<A, F1, B, F2, Rotation3>::new(Rotation3::IDENTITY);
//! ```
//!
//! `Translation3` cannot be constructed with different frames:
//!
//! ```compile_fail
//! use affn::ops::Translation3;
//! use affn::prelude::*;
//! use affn::transform::Transform;
//! use qtty::units::Meter;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct F1;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct F2;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct A;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct B;
//!
//! let _ = Transform::<A, F1, B, F2, Translation3<Meter>>::new(Translation3::new(
//!     0.0, 0.0, 0.0,
//! ));
//! ```
//!
//! Non-[`AffineCenter`] types cannot be used in center-changing transforms:
//!
//! ```compile_fail
//! use affn::ops::Translation3;
//! use affn::prelude::*;
//! use affn::transform::Transform;
//! use qtty::units::Meter;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct F;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct A;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! #[center(affine = false)]
//! struct NonAffine;
//!
//! let _ = Transform::<A, F, NonAffine, F, Translation3<Meter>>::new(Translation3::new(
//!     0.0, 0.0, 0.0,
//! ));
//! ```
//!
//! Incompatible composition fails to compile:
//!
//! ```compile_fail
//! use affn::ops::Rotation3;
//! use affn::prelude::*;
//! use affn::transform::Transform;
//!
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FA;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FB;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FC;
//! #[derive(Debug, Copy, Clone, ReferenceFrame)]
//! struct FD;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct A;
//! #[derive(Debug, Copy, Clone, ReferenceCenter)]
//! struct C;
//!
//! let ab = Transform::<A, FA, A, FB, Rotation3>::new(Rotation3::IDENTITY);
//! let cd = Transform::<C, FC, C, FD, Rotation3>::new(Rotation3::IDENTITY);
//! // A/FB does not match C/FC — this must not compile:
//! let _ = ab.then(cd);
//! ```

mod compose;

pub use compose::ComposeAfter;

use crate::cartesian::Position;
use crate::centers::{AffineCenter, ReferenceCenter};
use crate::frames::ReferenceFrame;
use crate::ops::{Isometry3, Rotation3, Translation3};
use qtty::length::LengthUnit;
use qtty::Quantity;
use std::marker::PhantomData;
use std::ops::Mul;

/// Phantom carrier for the four reference-system tags on [`Transform`].
///
/// Uses `fn() -> …` so the markers do not affect `Send`/`Sync` of the transform.
type SystemMarker<FromCenter, FromFrame, ToCenter, ToFrame> =
    PhantomData<fn() -> (FromCenter, FromFrame, ToCenter, ToFrame)>;

/// A typed transform between two reference systems.
///
/// The type parameters encode the source and destination systems; `Op` is the
/// underlying affine operator ([`Rotation3`], [`Translation3`], or
/// [`Isometry3`]).
///
/// Source/destination tags are zero-cost phantom data. See the [module-level
/// documentation](self) for application rules, composition, and the
/// parameterized-center limitation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Transform<FromCenter, FromFrame, ToCenter, ToFrame, Op> {
    op: Op,
    _marker: SystemMarker<FromCenter, FromFrame, ToCenter, ToFrame>,
}

/// Frame-only transform: same center, `FromFrame → ToFrame`, operator [`Rotation3`].
pub type FrameTransform<C, FromFrame, ToFrame> = Transform<C, FromFrame, C, ToFrame, Rotation3>;

/// Center-only transform: same frame, `FromCenter → ToCenter`, operator [`Translation3`].
pub type CenterTransform<FromCenter, ToCenter, F, U> =
    Transform<FromCenter, F, ToCenter, F, Translation3<U>>;

/// Rigid (center + frame) transform with operator [`Isometry3`].
pub type RigidTransform<FromCenter, FromFrame, ToCenter, ToFrame, U> =
    Transform<FromCenter, FromFrame, ToCenter, ToFrame, Isometry3<U>>;

impl<FromCenter, FromFrame, ToCenter, ToFrame, Op>
    Transform<FromCenter, FromFrame, ToCenter, ToFrame, Op>
{
    /// Internal constructor for composition and other in-crate paths where the
    /// shape invariant is already established by the input transforms.
    #[inline]
    const fn from_op_unchecked(op: Op) -> Self {
        Self {
            op,
            _marker: PhantomData,
        }
    }

    /// Returns a reference to the underlying affine operator.
    #[inline]
    #[must_use]
    pub const fn op(&self) -> &Op {
        &self.op
    }

    /// Consumes the transform and returns the underlying affine operator.
    #[inline]
    #[must_use]
    pub fn into_op(self) -> Op {
        self.op
    }

    /// Composes `self` with `next`, applying `self` first, then `next`.
    ///
    /// Type-level requirement: `next`'s source system must equal `self`'s
    /// destination system. The resulting transform is `From → next.To` with an
    /// operator produced by composing the two `Op` values.
    ///
    /// Mathematically this follows the existing operator convention
    /// `result = next * previous` (apply previous, then next). Mixed
    /// rotation/translation pairs promote to [`Isometry3`].
    #[inline]
    #[must_use]
    pub fn then<NextCenter, NextFrame, NextOp>(
        self,
        next: Transform<ToCenter, ToFrame, NextCenter, NextFrame, NextOp>,
    ) -> Transform<FromCenter, FromFrame, NextCenter, NextFrame, NextOp::Output>
    where
        NextOp: ComposeAfter<Op>,
    {
        Transform::from_op_unchecked(next.op.after(self.op))
    }
}

// =============================================================================
// Public constructors (valid shapes only)
// =============================================================================

impl<C, F1, F2> Transform<C, F1, C, F2, Rotation3>
where
    C: ReferenceCenter,
    F1: ReferenceFrame,
    F2: ReferenceFrame,
{
    /// Frame-only transform: same center `C`, rotation `F1 → F2`.
    ///
    /// Call as `Transform::<C, F1, C, F2, Rotation3>::new(op)` (or bind to a
    /// [`FrameTransform`] alias) so the compiler selects this constructor.
    #[inline]
    #[must_use]
    pub const fn new(op: Rotation3) -> Self {
        Self::from_op_unchecked(op)
    }
}

impl<C1, C2, F, U> Transform<C1, F, C2, F, Translation3<U>>
where
    C1: AffineCenter<Params = ()>,
    C2: AffineCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    /// Center-only transform: same frame `F`, translation `C1 → C2`.
    ///
    /// Requires [`AffineCenter`] on both centers. Use
    /// `Transform::<C1, F, C2, F, Translation3<U>>::new(op)`.
    #[inline]
    #[must_use]
    pub const fn new(op: Translation3<U>) -> Self {
        Self::from_op_unchecked(op)
    }
}

impl<C1, F1, C2, F2, U> Transform<C1, F1, C2, F2, Isometry3<U>>
where
    C1: AffineCenter<Params = ()>,
    C2: AffineCenter<Params = ()>,
    F1: ReferenceFrame,
    F2: ReferenceFrame,
    U: LengthUnit,
{
    /// Rigid transform: rotation and translation `C1/F1 → C2/F2`.
    ///
    /// Requires [`AffineCenter`] on both centers. Use
    /// `Transform::<C1, F1, C2, F2, Isometry3<U>>::new(op)`.
    #[inline]
    #[must_use]
    pub const fn new(op: Isometry3<U>) -> Self {
        Self::from_op_unchecked(op)
    }
}

// =============================================================================
// Application: Rotation3 (frame-only; preserves center params)
// =============================================================================

impl<C, F1, F2> Transform<C, F1, C, F2, Rotation3>
where
    C: ReferenceCenter,
    F1: ReferenceFrame,
    F2: ReferenceFrame,
{
    /// Applies this frame transform to a position in the source system.
    ///
    /// Center parameters are preserved. The result is tagged with `F2`.
    #[inline]
    #[must_use]
    pub fn apply<U: LengthUnit>(self, pos: Position<C, F1, U>) -> Position<C, F2, U>
    where
        C::Params: Clone,
    {
        (self.op * pos).reinterpret_frame()
    }

    /// Returns the inverse frame transform (`F2 → F1`, same center).
    #[inline]
    #[must_use]
    pub fn inverse(self) -> Transform<C, F2, C, F1, Rotation3> {
        Transform::<C, F2, C, F1, Rotation3>::from_op_unchecked(self.op.inverse())
    }
}

impl<C, F1, F2, U> Mul<Position<C, F1, U>> for Transform<C, F1, C, F2, Rotation3>
where
    C: ReferenceCenter,
    C::Params: Clone,
    F1: ReferenceFrame,
    F2: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Position<C, F2, U>;

    #[inline]
    fn mul(self, rhs: Position<C, F1, U>) -> Self::Output {
        self.apply(rhs)
    }
}

// =============================================================================
// Application: Translation3 (center-only; Params = () only)
// =============================================================================

impl<C1, C2, F, U> Transform<C1, F, C2, F, Translation3<U>>
where
    C1: AffineCenter<Params = ()>,
    C2: AffineCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    /// Applies this center transform to a position in the source system.
    ///
    /// Restricted to centers with `Params = ()` so destination parameters are
    /// never manufactured or discarded. See the [module docs](self).
    #[inline]
    #[must_use]
    pub fn apply(self, pos: Position<C1, F, U>) -> Position<C2, F, U> {
        let [x, y, z] = self
            .op
            .apply_array([pos.x().value(), pos.y().value(), pos.z().value()]);
        Position::new(
            Quantity::<U>::new(x),
            Quantity::<U>::new(y),
            Quantity::<U>::new(z),
        )
    }

    /// Returns the inverse center transform (`C2 → C1`, same frame).
    #[inline]
    #[must_use]
    pub fn inverse(self) -> Transform<C2, F, C1, F, Translation3<U>> {
        Transform::<C2, F, C1, F, Translation3<U>>::from_op_unchecked(self.op.inverse())
    }
}

impl<C1, C2, F, U> Mul<Position<C1, F, U>> for Transform<C1, F, C2, F, Translation3<U>>
where
    C1: AffineCenter<Params = ()>,
    C2: AffineCenter<Params = ()>,
    F: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Position<C2, F, U>;

    #[inline]
    fn mul(self, rhs: Position<C1, F, U>) -> Self::Output {
        self.apply(rhs)
    }
}

// =============================================================================
// Application: Isometry3 (center + frame; Params = () only)
// =============================================================================

impl<C1, F1, C2, F2, U> Transform<C1, F1, C2, F2, Isometry3<U>>
where
    C1: AffineCenter<Params = ()>,
    C2: AffineCenter<Params = ()>,
    F1: ReferenceFrame,
    F2: ReferenceFrame,
    U: LengthUnit,
{
    /// Applies this rigid transform to a position in the source system.
    ///
    /// Restricted to centers with `Params = ()`. See the [module docs](self).
    #[inline]
    #[must_use]
    pub fn apply(self, pos: Position<C1, F1, U>) -> Position<C2, F2, U> {
        let [x, y, z] = self
            .op
            .apply_point([pos.x().value(), pos.y().value(), pos.z().value()]);
        Position::new(
            Quantity::<U>::new(x),
            Quantity::<U>::new(y),
            Quantity::<U>::new(z),
        )
    }

    /// Returns the inverse rigid transform.
    #[inline]
    #[must_use]
    pub fn inverse(self) -> Transform<C2, F2, C1, F1, Isometry3<U>> {
        Transform::<C2, F2, C1, F1, Isometry3<U>>::from_op_unchecked(self.op.inverse())
    }
}

impl<C1, F1, C2, F2, U> Mul<Position<C1, F1, U>> for Transform<C1, F1, C2, F2, Isometry3<U>>
where
    C1: AffineCenter<Params = ()>,
    C2: AffineCenter<Params = ()>,
    F1: ReferenceFrame,
    F2: ReferenceFrame,
    U: LengthUnit,
{
    type Output = Position<C2, F2, U>;

    #[inline]
    fn mul(self, rhs: Position<C1, F1, U>) -> Self::Output {
        self.apply(rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DeriveReferenceCenter as ReferenceCenter, DeriveReferenceFrame as ReferenceFrame};
    use qtty::angular::Radians;
    use qtty::units::{Kilometer, Meter};
    use std::f64::consts::FRAC_PI_2;

    const EPSILON: f64 = 1e-12;

    fn make_rot<C, F1, F2>(op: Rotation3) -> Transform<C, F1, C, F2, Rotation3>
    where
        C: ReferenceCenter,
        F1: ReferenceFrame,
        F2: ReferenceFrame,
    {
        Transform::<C, F1, C, F2, Rotation3>::new(op)
    }

    fn make_trans<C1, C2, F, U>(op: Translation3<U>) -> Transform<C1, F, C2, F, Translation3<U>>
    where
        C1: AffineCenter<Params = ()>,
        C2: AffineCenter<Params = ()>,
        F: ReferenceFrame,
        U: LengthUnit,
    {
        Transform::<C1, F, C2, F, Translation3<U>>::new(op)
    }

    fn make_iso<C1, F1, C2, F2, U>(op: Isometry3<U>) -> Transform<C1, F1, C2, F2, Isometry3<U>>
    where
        C1: AffineCenter<Params = ()>,
        C2: AffineCenter<Params = ()>,
        F1: ReferenceFrame,
        F2: ReferenceFrame,
        U: LengthUnit,
    {
        Transform::<C1, F1, C2, F2, Isometry3<U>>::new(op)
    }

    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct FrameA;
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct FrameB;
    #[derive(Debug, Copy, Clone, ReferenceFrame)]
    struct FrameC;

    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct CenterA;
    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct CenterB;
    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    struct CenterC;

    #[derive(Clone, Debug, Default, PartialEq)]
    struct Site {
        id: i32,
    }

    #[derive(Debug, Copy, Clone, ReferenceCenter)]
    #[center(params = Site)]
    struct ParamCenter;

    fn assert_xyz_eq<C: crate::centers::ReferenceCenter, F: crate::frames::ReferenceFrame, U>(
        pos: &Position<C, F, U>,
        x: f64,
        y: f64,
        z: f64,
    ) where
        U: LengthUnit,
    {
        assert!(
            (pos.x().value() - x).abs() < EPSILON
                && (pos.y().value() - y).abs() < EPSILON
                && (pos.z().value() - z).abs() < EPSILON,
            "got ({}, {}, {}), expected ({x}, {y}, {z})",
            pos.x().value(),
            pos.y().value(),
            pos.z().value(),
        );
    }

    #[test]
    fn frame_only_transform() {
        let tf: FrameTransform<CenterA, FrameA, FrameB> =
            make_rot(Rotation3::rz(Radians::new(FRAC_PI_2)));
        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 0.0, 0.0);
        let out = tf.apply(pos);
        assert_xyz_eq(&out, 0.0, 1.0, 0.0);
    }

    #[test]
    fn center_only_transform() {
        let tf: CenterTransform<CenterA, CenterB, FrameA, Meter> =
            make_trans(Translation3::new(1.0, 2.0, 3.0));
        let pos = Position::<CenterA, FrameA, Meter>::new(10.0, 20.0, 30.0);
        let out = tf.apply(pos);
        assert_xyz_eq(&out, 11.0, 22.0, 33.0);
    }

    #[test]
    fn combined_center_and_frame_transform() {
        let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
        let trans = Translation3::<Meter>::new(10.0, 0.0, 0.0);
        let tf: RigidTransform<CenterA, FrameA, CenterB, FrameB, Meter> =
            make_iso(Isometry3::new(rot, trans));
        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 0.0, 0.0);
        // R*(1,0,0)=(0,1,0), then +t → (10,1,0)
        let out = tf.apply(pos);
        assert_xyz_eq(&out, 10.0, 1.0, 0.0);
    }

    #[test]
    fn rotation_composition() {
        let ab: FrameTransform<CenterA, FrameA, FrameB> =
            make_rot(Rotation3::rz(Radians::new(FRAC_PI_2)));
        let bc: FrameTransform<CenterA, FrameB, FrameC> =
            make_rot(Rotation3::rz(Radians::new(FRAC_PI_2)));
        let ac = ab.then(bc);

        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 0.0, 0.0);
        let sequential = bc.apply(ab.apply(pos));
        let composed = ac.apply(pos);
        assert_xyz_eq(&sequential, -1.0, 0.0, 0.0);
        assert_xyz_eq(&composed, -1.0, 0.0, 0.0);
    }

    #[test]
    fn translation_composition() {
        let ab: CenterTransform<CenterA, CenterB, FrameA, Meter> =
            make_trans(Translation3::new(1.0, 0.0, 0.0));
        let bc: CenterTransform<CenterB, CenterC, FrameA, Meter> =
            make_trans(Translation3::new(0.0, 2.0, 0.0));
        let ac = ab.then(bc);

        let pos = Position::<CenterA, FrameA, Meter>::new(0.0, 0.0, 0.0);
        let sequential = bc.apply(ab.apply(pos));
        let composed = ac.apply(pos);
        assert_xyz_eq(&sequential, 1.0, 2.0, 0.0);
        assert_xyz_eq(&composed, 1.0, 2.0, 0.0);
    }

    #[test]
    fn rotation_then_translation_composition() {
        // Apply rotation (frame A→B, same center), then translation (center A→B in frame B).
        let rot: FrameTransform<CenterA, FrameA, FrameB> =
            make_rot(Rotation3::rz(Radians::new(FRAC_PI_2)));
        let trans: CenterTransform<CenterA, CenterB, FrameB, Meter> =
            make_trans(Translation3::new(10.0, 0.0, 0.0));
        let composed = rot.then(trans);

        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 0.0, 0.0);
        let sequential = trans.apply(rot.apply(pos));
        let via_composed = composed.apply(pos);
        assert_xyz_eq(&sequential, 10.0, 1.0, 0.0);
        assert_xyz_eq(&via_composed, 10.0, 1.0, 0.0);
    }

    #[test]
    fn translation_then_rotation_composition() {
        // Apply translation (center A→B in frame A), then rotation (frame A→B).
        let trans: CenterTransform<CenterA, CenterB, FrameA, Meter> =
            make_trans(Translation3::new(1.0, 0.0, 0.0));
        let rot: FrameTransform<CenterB, FrameA, FrameB> =
            make_rot(Rotation3::rz(Radians::new(FRAC_PI_2)));
        let composed = trans.then(rot);

        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 0.0, 0.0);
        // sequential: translate (1,0,0)+(1,0,0)=(2,0,0), rotate → (0,2,0)
        let sequential = rot.apply(trans.apply(pos));
        let via_composed = composed.apply(pos);
        assert_xyz_eq(&sequential, 0.0, 2.0, 0.0);
        assert_xyz_eq(&via_composed, 0.0, 2.0, 0.0);
    }

    #[test]
    fn isometry_composition() {
        let ab: RigidTransform<CenterA, FrameA, CenterB, FrameB, Meter> = make_iso(Isometry3::new(
            Rotation3::rz(Radians::new(FRAC_PI_2)),
            Translation3::new(1.0, 0.0, 0.0),
        ));
        let bc: RigidTransform<CenterB, FrameB, CenterC, FrameC, Meter> = make_iso(Isometry3::new(
            Rotation3::rx(Radians::new(FRAC_PI_2)),
            Translation3::new(0.0, 1.0, 0.0),
        ));
        let ac = ab.then(bc);

        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 2.0, 3.0);
        let sequential = bc.apply(ab.apply(pos));
        let composed = ac.apply(pos);
        assert!((sequential.x().value() - composed.x().value()).abs() < EPSILON);
        assert!((sequential.y().value() - composed.y().value()).abs() < EPSILON);
        assert!((sequential.z().value() - composed.z().value()).abs() < EPSILON);
    }

    #[test]
    fn sequential_equals_composed_mixed_ops() {
        let r1: FrameTransform<CenterA, FrameA, FrameB> =
            make_rot(Rotation3::ry(Radians::new(0.3)));
        let t: CenterTransform<CenterA, CenterB, FrameB, Meter> =
            make_trans(Translation3::new(0.5, -1.0, 2.0));
        let r2: FrameTransform<CenterB, FrameB, FrameC> =
            make_rot(Rotation3::rx(Radians::new(-0.7)));

        let composed = r1.then(t).then(r2);
        let pos = Position::<CenterA, FrameA, Meter>::new(1.25, -0.5, 3.0);
        let sequential = r2.apply(t.apply(r1.apply(pos)));
        let via_composed = composed.apply(pos);
        assert!((sequential.x().value() - via_composed.x().value()).abs() < EPSILON);
        assert!((sequential.y().value() - via_composed.y().value()).abs() < EPSILON);
        assert!((sequential.z().value() - via_composed.z().value()).abs() < EPSILON);
    }

    #[test]
    fn frame_only_preserves_parameterized_center_params() {
        let site = Site { id: 42 };
        let pos =
            Position::<ParamCenter, FrameA, Meter>::new_with_params(site.clone(), 1.0, 0.0, 0.0);
        let tf: FrameTransform<ParamCenter, FrameA, FrameB> =
            make_rot(Rotation3::rz(Radians::new(FRAC_PI_2)));
        let out = tf.apply(pos);
        assert_eq!(out.center_params(), &site);
        assert_xyz_eq(&out, 0.0, 1.0, 0.0);
    }

    #[test]
    fn units_are_compile_time_checked_and_preserved() {
        let tf: CenterTransform<CenterA, CenterB, FrameA, Kilometer> =
            make_trans(Translation3::new(1.5, 0.0, 0.0));
        let pos = Position::<CenterA, FrameA, Kilometer>::new(2.0, 0.0, 0.0);
        let out = tf.apply(pos);
        assert_xyz_eq(&out, 3.5, 0.0, 0.0);
        // to_unit still works on the result
        let meters: Position<CenterB, FrameA, Meter> = out.to_unit();
        assert!((meters.x().value() - 3500.0).abs() < EPSILON);
    }

    #[test]
    fn mul_operator_matches_apply() {
        let tf: FrameTransform<CenterA, FrameA, FrameB> =
            make_rot(Rotation3::rz(Radians::new(FRAC_PI_2)));
        let pos = Position::<CenterA, FrameA, Meter>::new(0.0, 1.0, 0.0);
        let via_apply = tf.apply(pos);
        let via_mul = tf * pos;
        assert_xyz_eq(&via_apply, -1.0, 0.0, 0.0);
        assert_xyz_eq(&via_mul, -1.0, 0.0, 0.0);
    }

    #[test]
    fn inverse_roundtrip_frame() {
        let tf: FrameTransform<CenterA, FrameA, FrameB> =
            make_rot(Rotation3::rz(Radians::new(0.42)));
        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 2.0, 3.0);
        let roundtrip = tf.inverse().apply(tf.apply(pos));
        assert_xyz_eq(&roundtrip, 1.0, 2.0, 3.0);
    }

    #[test]
    fn inverse_roundtrip_center() {
        let tf: CenterTransform<CenterA, CenterB, FrameA, Meter> =
            make_trans(Translation3::new(1.0, 2.0, 3.0));
        let pos = Position::<CenterA, FrameA, Meter>::new(4.0, 5.0, 6.0);
        let roundtrip = tf.inverse().apply(tf.apply(pos));
        assert_xyz_eq(&roundtrip, 4.0, 5.0, 6.0);
    }

    #[test]
    fn inverse_roundtrip_rigid() {
        let tf: RigidTransform<CenterA, FrameA, CenterB, FrameB, Meter> = make_iso(Isometry3::new(
            Rotation3::rz(Radians::new(FRAC_PI_2)),
            Translation3::new(0.0, 1.0, 0.0),
        ));
        let pos = Position::<CenterA, FrameA, Meter>::new(1.0, 0.0, 0.0);
        let roundtrip = tf.inverse().apply(tf.apply(pos));
        assert_xyz_eq(&roundtrip, 1.0, 0.0, 0.0);
    }

    #[test]
    fn into_op_and_op_accessors() {
        let rot = Rotation3::rz(Radians::new(FRAC_PI_2));
        let tf: FrameTransform<CenterA, FrameA, FrameB> = make_rot(rot);
        assert_eq!(tf.op(), &rot);
        assert_eq!(tf.into_op(), rot);
    }

    #[test]
    fn wrong_center_application_is_type_error() {
        // Documented via rustdoc compile_fail; this test only checks the happy path
        // still distinguishes centers at the type level by requiring an explicit tag.
        let tf: CenterTransform<CenterA, CenterB, FrameA, Meter> =
            make_trans(Translation3::new(1.0, 0.0, 0.0));
        let pos = Position::<CenterA, FrameA, Meter>::new(0.0, 0.0, 0.0);
        let _: Position<CenterB, FrameA, Meter> = tf.apply(pos);
    }
}
