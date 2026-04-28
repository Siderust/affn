# RFC: Unifying the `algebra` and `cartesian` Geometry Kernels

- **RFC**: kernel-unification
- **Status**: Draft
- **Audit issue**: 7
- **Todo**: `kernel-unify-design`
- **Proposal**: 7A, phase 1 (design only — no source changes)
- **Scope**: `affn` crate (kernels under `src/algebra.rs`, `src/cartesian/*`,
  `src/planar/*`, `src/ops/*`)

---

## Status

Draft. This document captures the design intent and trade-offs for a
single-kernel rewrite. No `src/` files are touched in this phase. Phases
2 and 3 (implementation behind a feature flag, then migration) are out
of scope for this RFC's deliverable but sketched at the end.

---

## Motivation

`affn` today carries **two parallel geometry kernels** that overlap in
purpose, diverge in API, and together block several roadmap items.

### Kernel A — `algebra` (N-dim, dimension-generic)

- File: `src/algebra.rs:1-799`.
- Marker trait: `Space: Copy + Clone + Debug` at
  `src/algebra.rs:30`.
- Core types:
  - `Vector<Sp: Space, U: Unit, const N: usize>` at
    `src/algebra.rs:39-44` — `#[repr(transparent)]` over
    `[Quantity<U>; N]`.
  - `Point<Sp: Space, U: Unit, const N: usize>` at
    `src/algebra.rs:51-56` — same shape.
- Aliases `Point1/2/3`, `Vector1/2/3` at `src/algebra.rs:58-70`.
- Affine algebra: `Sub for Point` returns `Vector` at
  `src/algebra.rs:361-371`; `Add<Vector> for Point` at
  `src/algebra.rs:372-382`; no `Add<Point, Point>` impl exists, so
  `P + P` is a compile error as required.
- Has additional 1-D facilities (`SplitQuantity`, `SplitPoint1`,
  `AffineMap1`) at `src/algebra.rs:416-799` used by `tempoch`.
- The 2-D consumer is `planar`: `src/planar/mod.rs:25` imports
  `Point2`, `Vector2`, `Space`, and wraps them in
  `PlanarSpace<C, F>` (`src/planar/mod.rs:33-36`) and
  `FrameSpace<F>` (`src/planar/mod.rs:38-41`).

### Kernel B — `cartesian` (3-D only, frame/center-aware, nalgebra-backed)

- Module overview: `src/cartesian/mod.rs:1-119`.
- Internal storage: `XYZ<T>(pub(crate) Vector3<T>)` at
  `src/cartesian/xyz.rs:35-45`, `#[repr(transparent)]` over
  `nalgebra::Vector3<T>`.
- Public types:
  - `Position<C, F, U>` at `src/cartesian/position.rs:128-133`
    — wraps `XYZ<Quantity<U>>` plus an inline `center_params: C::Params`
    field.
  - `Vector<F, U>` at `src/cartesian/vector.rs:70-75` — wraps
    `XYZ<Quantity<U>>`. Aliased as `Displacement<F, U>` /
    `Velocity<F, U>` at `src/cartesian/vector.rs:359-369`.
  - `Direction<F>` at `src/cartesian/direction.rs:97-102` — wraps a
    raw `XYZ<f64>` (no unit, normalized).
- Affine algebra duplicated from kernel A in `position.rs` (e.g.
  `Sub for Position` at `src/cartesian/position.rs:427-450`,
  `Add<Displacement> for Position` at
  `src/cartesian/position.rs:498-515`).

### Evidence of duplication

| Concept | Kernel A (`algebra`) | Kernel B (`cartesian`) |
|---|---|---|
| Affine point | `Point<Sp, U, N>` (`algebra.rs:51`) | `Position<C, F, U>` (`position.rs:128`) |
| Free vector | `Vector<Sp, U, N>` (`algebra.rs:39`) | `Vector<F, U>` (`vector.rs:70`) |
| Storage | `[Quantity<U>; N]` | `XYZ<T>` → `nalgebra::Vector3<T>` (`xyz.rs:45`) |
| `P − P → V` | `algebra.rs:361-371` | `position.rs:427-450` |
| `P + V → P` | `algebra.rs:372-382` | `position.rs:498-515` |
| Unit conversion | `to_unit` (`algebra.rs:124-128`, `:177-182`) | `to_unit` (`vector.rs:157-163`, `position.rs:~290`) |
| Negation / scaling | `algebra.rs:115-128, :330-359` | `vector.rs:195-220, :270-298` |

Two test suites exist for the same algebra (`vector_arithmetic`,
`affine_position_ops` in `planar/mod.rs:487-499, 449-458` mirror tests
in `cartesian/{vector,position}.rs`).

### Center::Params side-channel

`Position` carries an inline `C::Params` (`position.rs:130`) that does
not exist in kernel A's `Point`. The trait is defined at
`src/centers.rs:80-86`:

```rust
pub trait ReferenceCenter: Copy + Clone + std::fmt::Debug {
    type Params: Clone + Debug + Default + PartialEq;
    fn center_name() -> &'static str;
}
```

Most centers use `Params = ()` (zero size), but parameterized centers
(e.g. topocentric observer sites) need real runtime data, and operators
must thread it through every transform — see e.g. the `Mul<Position>`
impls at `src/ops/mod.rs:139-208` that all clone `rhs.center_params()`
to rebuild the result.

### Costs

1. **Duplicate impls.** Every operator macro in `src/ops/mod.rs` has
   to re-implement `Mul<Position>`, `Mul<Vector>`, `Mul<Direction>`
   (see `impl_position_mul!` at `src/ops/mod.rs:139-164` and the
   per-operator copies at `:168-208`). A unified kernel allows one
   blanket impl per operator type.
2. **API drift.** `algebra::Point2::new(x, y)` (`algebra.rs:251`),
   `cartesian::Position::new(x, y, z)` (`position.rs:237`), and
   `planar::Position::new(x, y)` (`planar/mod.rs:239`) each have
   slightly different constructor surfaces and different relationships
   to `Center::Params`.
3. **Two 2-D code paths.** `planar` already wraps kernel A
   (`planar/mod.rs:25`); `cartesian` ignores it and re-implements the
   same algebra over 3-component nalgebra vectors. Bug fixes have to
   be mirrored.
4. **Center::Params not modeled in algebra.** Kernel A has no notion of
   `Center::Params`; `planar::Position` re-introduces the field
   (`planar/mod.rs:58-61`) outside the algebra type. There is no single
   place to enforce "subtraction of points with mismatched params is an
   error" — `cartesian::Position` panics at
   `src/cartesian/position.rs:444-449`, while `planar::Position` panics
   at `src/planar/mod.rs:254-258`. They are independent implementations
   of the same rule.

### Blocked extensions

- **4-D spacetime point** (e.g. `Position4<C, F, U>` for a Minkowski
  event with time as the 4th coordinate). Kernel A supports `N = 4`
  trivially (the type is already generic at `algebra.rs:51`). Kernel
  B's `XYZ` is hard-wired to `nalgebra::Vector3` (`xyz.rs:45`), so
  every operator and every `apply_array([f64; 3])` signature
  (`src/ops/translation.rs:91-94`, `src/ops/rotation.rs` `apply_array`,
  `src/ops/isometry.rs:121-124`) would need a parallel 4-D copy.
- **6-D state vectors** (position + velocity, common in orbit
  propagation). Today the canonical representation requires a pair
  `(Position<C,F,U>, Vector<F, V>)`, with no shared `Point<…, 6>`.
  A unified `Point<Space3, U, N>` would let consumers express
  `Point<PhaseSpace<C,F>, U_phase, 6>` once.
- **N-dim test fixtures and BLAS code-gen** (`siderust` precession
  pipelines that today use kernel A only for time, not for spatial
  state).

---

## Goals

1. **One canonical N-dim affine kernel.** A single
   `Point<Space, U, N>` and `Vector<Space, U, N>` parameterised by a
   `Space` marker (which encodes `Center`, `Frame`, and `Params`
   together) and the dimension `N`.
2. **Center / frame / params live in `Space`.** Existing `cartesian`
   public APIs (`Position<C, F, U>`, `Vector<F, U>`, `Direction<F>`)
   become **transparent type aliases** over the unified kernel during
   migration, so downstream code (siderust, FFI, adapters) keeps
   compiling unchanged.
3. **Zero-cost.** Unified types remain `#[repr(transparent)]` over the
   underlying storage (matching the current `xyz.rs:44-45` and
   `vector.rs:70-75` guarantee). No heap allocation; no extra fields
   beyond what `Position` carries today.
4. **Open the door to N=4 and N=6** without further kernel rewrites.
   `Point<…, 4>` and `Point<…, 6>` must compile and support the
   affine algebra (subtraction → vector, translation → point) on
   day one.
5. **Preserve the affn invariants** documented in `cartesian/mod.rs`:
   `Position − Position → Displacement`, `Position + Position` is a
   compile error, `Direction + Direction` is a compile error, no
   `Center` transform on `Direction`.

## Non-goals

- **Removing `nalgebra`.** Kernel B's BLAS hookup
  (`xyz.rs:148, :118-119`, used by `Vector::magnitude`,
  `Direction::renormalize`, `Rotation3::apply_xyz`) stays. The
  unified kernel must keep an N=3 specialization that backs onto
  `nalgebra::Vector3`.
- **Replacing `qtty`.** `Quantity<U>` remains the component type.
- **Touching the curvilinear kernels** — `src/conic`,
  `src/spherical`, `src/ellipsoidal`, `src/ellipsoid.rs`. These are
  out of scope; only the rectilinear affine kernel is unified.
- **Breaking the public API in 0.6.x.** The unified kernel ships
  behind a feature flag (`unified-kernel`); 0.7 removes the legacy
  paths.

---

## Design questions

Each subsection states a question, two candidate answers, and trade-offs.

### Q1. How does `Center::Params` runtime data live in an N-dim Point?

`ReferenceCenter::Params` (`centers.rs:81-83`) is potentially a real
struct (e.g. an observer site) and must be reachable from operations
on `Position`.

**Candidate A — Side-channel field on the kernel type.**
Mirror today's `cartesian::Position` (`position.rs:128-133`):

```rust
#[repr(C)]
pub struct Point<Sp: Space, U: Unit, const N: usize>
where Sp: SpaceWithParams,
{
    coordinates: [Quantity<U>; N],
    params: Sp::Params,
}
```

- Pro: matches today's data layout exactly; trivial migration; the
  side-channel is invisible to operators that don't care about it.
- Pro: when `Sp::Params = ()` the field is ZST and the type is
  `#[repr(transparent)]`-equivalent — same memory as today's
  `XYZ<Quantity<U>>`.
- Con: every `Point` must thread `Sp::Params` through, even when the
  space is "free vector" (no center). `Vector` therefore needs a
  different `Sp` bound (one without `Params`).
- Con: blocks future "unified Vector and Point in one type" since
  vectors must not carry params.

**Candidate B — `SpaceWithParams` supertrait + opt-in carrier.**
Split the `Space` marker (`algebra.rs:30`) into two traits:

```rust
pub trait Space: Copy + Clone + Debug {}
pub trait AffineSpace: Space { type Params: Clone + Debug + Default + PartialEq; }
```

Only `Point<Sp, U, N>` requires `Sp: AffineSpace` and stores
`Sp::Params`. `Vector<Sp, U, N>` only requires `Sp: Space` and stores
no params. This is the natural generalization of today's
`NoCenter` / `AffineCenter` distinction in `centers.rs:124-151`.

- Pro: cleanly captures the "free vectors have no center" rule at the
  trait level, exactly as the existing `AffineCenter` marker
  (`centers.rs:151`) intends.
- Pro: kernel A's existing `planar::FrameSpace<F>` /
  `PlanarSpace<C, F>` distinction (`planar/mod.rs:33-41`) is
  literally this pattern, so we are formalizing what `planar`
  already does.
- Con: two traits to teach; downstream impls of `Space` must decide
  which to implement.

**Candidate C — Generic storage parameter.**
`Point<Sp, U, N, Storage = DefaultStorage<U, N>>` where `Storage`
absorbs the params (e.g. `WithParams<P>`).

- Pro: maximum flexibility.
- Pro: `Direction` and `Position` can share a single `Point<Sp, U, N,
  Storage>` if `Storage` is generic enough.
- Con: large blast radius in type signatures everywhere; harder to
  read; `where`-clause noise. Unlikely to be worth it.

**Recommendation.** Candidate B (`SpaceWithParams` supertrait). It is
a small extension of the existing `Space` trait, mirrors
`AffineCenter` (`centers.rs:151`) and what `planar` already does,
and keeps `Vector` and `Point` correctly distinguished at the type
level.

### Q2. Do `Vector<F,U>` and `Direction<F>` collapse into one parametric type?

Today `Vector<F, U>` (`vector.rs:70`) carries a unit and a frame;
`Direction<F>` (`direction.rs:97-102`) carries only a frame and
internally stores `XYZ<f64>` (no unit, magnitude ≈ 1).

**Candidate A — Single parametric type:**

```rust
pub struct Vector<Sp, U, const N: usize, Norm = Free> { … }
pub enum Free {}
pub enum UnitNormalized {}

pub type Direction<Sp, const N: usize = 3> = Vector<Sp, Dimensionless, N, UnitNormalized>;
```

Norm-aware methods are written once (`normalize` only for `Norm =
Free` and `U: LengthUnit`; renormalization only for `Norm =
UnitNormalized`).

- Pro: kills the duplicate magnitude / scale / negate impls between
  `vector.rs:182-220` and `direction.rs:227-…`.
- Pro: rotation impls collapse: today
  `Rotation3 * Direction<F>` (`ops/mod.rs:237-246`) and `Rotation3 *
  Vector<F, U>` (`ops/mod.rs:214-230`) are separate; one
  `Mul<Vector<Sp, U, N, Norm>>` blanket impl covers both.
- Con: `Direction` no longer has its own type identity in error
  messages; rustdoc may show the alias expanded.
- Con: methods that exist *only* for one norm (e.g. `try_new`
  returning `Option<Direction>` from a free vector) require careful
  trait bounds (`U: LengthUnit, Norm: From<NormalizationOf<U>>`).

**Candidate B — Keep two structs, share storage only.**
Have `Vector` and `Direction` both wrap the unified `Point`/`Vector`
storage but remain distinct nominal types.

- Pro: minimum API churn; existing rustdoc and error messages
  preserved.
- Pro: norm-only methods stay where they are with no `where`-clause
  gymnastics.
- Con: still two sets of `Mul` impls; still two `magnitude`-like
  helpers.

**Recommendation.** Candidate A, but with the legacy aliases
`Vector<F, U> = Vector<FrameSpace<F>, U, 3, Free>` and
`Direction<F> = Vector<FrameSpace<F>, Dimensionless, 3, UnitNormalized>`
exported from `cartesian` so existing code keeps compiling. The norm
parameter is the same idea kernel A's `planar::Direction` skips today
(`planar/mod.rs:65-69` stores `[f64; 2]`); unifying makes that
deliberate rather than ad-hoc.

### Q3. How does `XYZ` survive?

`XYZ<T>` (`xyz.rs:35-45`) is `#[repr(transparent)]` over
`nalgebra::Vector3<T>` and is the linchpin of the BLAS hookup.

**Candidate A — `repr(transparent)` alias of the unified storage.**
For `N = 3`, the unified kernel's storage *is*
`nalgebra::Vector3<Quantity<U>>` and `pub type XYZ<T> = Storage3<T>`.
All existing `XYZ` constructors and methods (`xyz.rs:51-323`) re-export
unchanged.

- Pro: zero source change for downstream users of `XYZ`.
- Pro: `as_vec3()` / `from_vec3()` (`xyz.rs:60-73`) stay one-to-one
  with `nalgebra::Vector3`.
- Con: requires the unified kernel to expose a 3-D specialization of
  its storage that *is* `nalgebra::Vector3<T>`, not a generic
  `[Quantity<U>; 3]`. See Q4.

**Candidate B — Absorbed.**
Replace `XYZ<T>` everywhere with the new `Point`/`Vector` and delete
the type. Op modules currently take `XYZ<f64>` arguments
(`ops/translation.rs:65-67, :98-101`, `ops/isometry.rs:128-131`,
`ops/rotation.rs apply_xyz`) and would have to be rewritten.

- Pro: one fewer type to teach.
- Con: large blast radius; breaks any FFI consumer that already
  imported `XYZ`; loses the convenient "raw, untyped 3-vector for
  numerics" role that `XYZ<f64>` plays inside `ops/*`.

**Recommendation.** Candidate A. Keep `XYZ<T>` as a
`repr(transparent)` alias of the unified 3-D storage. Behaviorally
identical, no migration cost, and preserves the role `XYZ<f64>` plays
as a "raw numerical 3-vector" inside the operator implementations.

### Q4. nalgebra storage hookup for `N = 3` — specialised impl or always `[Quantity<U>; N]`?

Kernel A stores `[Quantity<U>; N]` (`algebra.rs:42, :54`); kernel B
stores `nalgebra::Vector3<T>` (`xyz.rs:45`) and uses BLAS-backed
operations such as `Vector3::magnitude`, `Vector3::cross`, and
`Vector3::normalize` (`xyz.rs:118-119, :136, :156`).

**Candidate A — Always `[Quantity<U>; N]`, with N=3 helpers.**
Storage is uniform; for N=3, expose `as_vec3()` /  `from_vec3()` that
*reinterpret* the array as a `nalgebra::Vector3` (sound because
`nalgebra::Vector3<T>` is itself `repr(transparent)` over `[T; 3]`
in current versions, but this is not formally guaranteed across
nalgebra releases).

- Pro: simplest type definition; one storage backend.
- Con: depends on a layout coincidence in nalgebra; brittle.
- Con: `magnitude_squared` etc. would have to be re-implemented as a
  loop, losing whatever vectorisation `nalgebra` provides for N=3.

**Candidate B — Trait-dispatched storage with an N=3 specialization.**
Introduce an internal `trait Storage<U: Unit, const N: usize>` with
two implementations:

- generic: `ArrayStorage<U, N>` wrapping `[Quantity<U>; N]`;
- 3-D: `XyzStorage<U>` wrapping `nalgebra::Vector3<Quantity<U>>` —
  the role `XYZ` plays today.

`Point` and `Vector` pick the storage by `N` via a
`DefaultStorage<U, N>` type alias (a `min_specialization`-free
mapping in const-generics).

- Pro: keeps the BLAS-backed N=3 code path that today's `xyz.rs:118,
  :136, :156` rely on.
- Pro: N=4, N=6 fall through to `ArrayStorage` automatically; no
  perf regression for the existing 3-D astronomy paths.
- Con: more type machinery; two storage backends to test.

**Recommendation.** Candidate B. The N=3 BLAS hookup is the entire
reason kernel B exists in its current form; throwing it away to win a
prettier type signature is the wrong trade. The specialization is
internal and invisible to users, who continue to see `Position`,
`Vector`, and `Direction`.

### Q5. Operators (`Rotation3`, `Translation3`, `Isometry3`) — stay 3-D-specific or become `RotationN<N>`?

Today's ops are explicitly 3-D: `Rotation3` is a 3×3 matrix
(`ops/rotation.rs:34-39`), `Translation3<U>` is `[f64; 3]`
(`ops/translation.rs:28-33`), `Isometry3<U>` is the pair
(`ops/isometry.rs:37-44`). The 2-D variants exist as
`Rotation2/Translation2/Isometry2` (`ops/mod.rs:46-51`).

**Candidate A — Keep them N-specific.**
Add `Rotation4`, `Translation4<U>`, `Isometry4<U>` only when needed.

- Pro: matrix code stays unrolled and easy to read; no surprising
  performance cliffs.
- Pro: semantics for "rotation" in 4-D (Lorentz boosts? plane
  rotations?) are domain-specific and don't generalize; refusing to
  pretend otherwise is honest.
- Con: linear growth in operator surface as N grows.

**Candidate B — Generic `RotationN<const N: usize>` etc.**
Single type covers all dimensions; specialise apply paths for N=2, 3.

- Pro: matches the kernel unification narrative.
- Con: rotation in arbitrary N is mathematically heterogeneous. The
  current `Rotation3::rx/ry/rz` (`ops/rotation.rs`) constructors don't
  generalize cleanly. We would expose constructors that exist only
  for some N.
- Con: code generation / specialization machinery for what is mostly
  a 3-D crate today.

**Recommendation.** Candidate A. Operators stay N-specific. The
unified kernel buys us 4-D and 6-D *coordinates* (where the algebra is
genuinely uniform: subtraction, translation, scaling), not 4-D
*rotations*. When and if we need spacetime boosts, they will be a new
operator type.

---

## Phases

1. **Phase 1 — Design (this RFC).** Docs only; no `src/` changes.
2. **Phase 2 — Implement behind `unified-kernel` feature flag.**
   - Introduce `affn::kernel` module with the unified `Space`,
     `AffineSpace`, `Point<Sp, U, N>`, `Vector<Sp, U, N, Norm>`, and
     `Storage` trait.
   - Re-implement `cartesian::{Position, Vector, Direction}` and
     `planar::{Position, Vector, Direction}` as transparent aliases /
     thin wrappers over the kernel.
   - Keep `XYZ<T>` as a re-export of the N=3 storage (Q3 / Q4).
   - Operator impls in `src/ops/*` keep their public signatures but
     are reduced to one blanket per operator (Q2, Q5).
   - Both kernels coexist; CI builds with and without
     `--features unified-kernel`.
3. **Phase 3 — Migration.**
   - Switch `siderust` to the unified kernel internally; verify
     numerical parity on precession and observer pipelines.
   - Update `siderust-ffi`, `qtty-ffi`, `tempoch-ffi` and the adapter
     surfaces (per the rule in `rust/AGENTS.md`).
   - Vendored copies in adapter repos sync separately.
   - `affn 0.7` removes the legacy `algebra::Point/Vector` and the
     stand-alone `cartesian` impls; the public `Position`,
     `Vector`, `Direction` aliases remain.

---

## Risks

- **Monomorphization bloat / inlining regression.** The unified
  `Vector<Sp, U, N, Norm>` exposes more generic parameters than
  today's `Vector<F, U>`. Wrong trait-dispatch design could turn
  inlinable 3×3 matrix multiplies into virtual dispatch.
  *Mitigation:* benchmark the precession and observer pipelines in
  `siderust` (already the most operator-heavy paths) before and after
  Phase 2 lands; require parity within 2 % wall-clock.
- **Breaking change cascade across adapters.** Even API-compatible
  changes can break vendored copies in adapter repos.
  *Mitigation:* `unified-kernel` is opt-in for one full minor cycle
  (0.6.x); 0.7 is the first release that removes the legacy paths.
- **Loss of `nalgebra` BLAS hooks for N=3.** Naively storing
  `[Quantity<U>; 3]` everywhere would regress operations that today
  use `Vector3::magnitude` and friends (`xyz.rs:118-119, :136`).
  *Mitigation:* the Q4 specialization keeps `XYZ` shape for N=3.

---

## Open questions

- **Interaction with qtty `U^2` work (audit issue 1).** A correct
  `magnitude_squared` for a `Vector<…, U>` should return
  `Quantity<U^2>`, not `f64` as today (`xyz.rs:262-267, :191-193`).
  When `qtty` gains squared units, the unified kernel should pick
  them up — but if `qtty` ships its `U^2` API after Phase 2 starts,
  do we land kernel unification with the current `f64` return and
  upgrade later, or block on `qtty`?
- **Ordering vs `affn-core` / `affn-astro` split (audit issue 8B).**
  If 8B happens first, the unified kernel lives in `affn-core` from
  day one and the `astro`-feature centers in `centers.rs` move to
  `affn-astro`. If 8B happens later, the kernel lands in `affn` and
  the split is a follow-up move. Phase ordering across issues 7 and
  8B is not yet resolved.

---

## References

- `affn` audit & remediation plan, issue 7:
  `/home/valles/.copilot/session-state/85c3aded-de62-4880-8d36-543b3058298b/plan.md`
- Source files cited inline:
  - `rust/affn/src/algebra.rs`
  - `rust/affn/src/cartesian/{mod.rs, xyz.rs, position.rs, vector.rs, direction.rs}`
  - `rust/affn/src/planar/mod.rs`
  - `rust/affn/src/centers.rs`
  - `rust/affn/src/frames/mod.rs`
  - `rust/affn/src/ops/{mod.rs, rotation.rs, translation.rs, isometry.rs}`
- Repository conventions: `rust/AGENTS.md`.
