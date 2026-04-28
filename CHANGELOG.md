# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed
- `Position::Sub`, `&Position - &Position`, and `Position::distance_to` now emit a structured panic message including the center type name (`std::any::type_name::<C>()`) and a debug print of both `center_params` values, and explicitly point users to the fallible `Position::checked_sub` / `Position::try_distance_to` alternatives. The panicking variant is scheduled to require `C::Params = ()` in affn 0.7; this 0.6 release only improves diagnostics and does not change any signatures or trait bounds.

## [0.6.1 - 2026-04-25]

### Fixed
- Restored API-compatible `new_raw` / `new_raw_with_params` aliases for spherical positions and directions while keeping the clearer `new_unchecked` names available.
- Restored `Rotation3::from_matrix` as an unchecked compatibility constructor and added finite-input rejection to `Rotation3::try_from_matrix`.
- Fixed spherical pole-crossing canonicalization so angles such as `polar = 100°` also rotate azimuth by `180°`, preserving the represented direction.
- Canonical spherical position construction now maps negative distances to the equivalent positive distance at the antipodal direction.
- Updated `affn-derive` frame-specific constructors to use the same spherical canonicalization rules as the core crate.
- Fixed `qtty` dependency metadata so the `astro` feature resolves against `qtty 0.6.1` in standalone builds and CI.

### Changed
- `Translation3` and `Isometry3` now carry the translation unit as a zero-cost type parameter with a `Meter` default for source compatibility.
- `Translation3::as_quantities::<U>()` now performs real unit conversion instead of re-wrapping raw magnitudes.
- CI check, clippy, test, and doctest commands now validate all feature combinations used by release builds.
- README feature/version guidance now matches the actual `0.6.x` public API.

## [0.6.0 - 2026-03-31]

### Added
- `#[repr(transparent)]` on `Direction<F>`, `Vector<F, U>`, `TypedPeriapsisParam<U, K>`, and `TypedSemiMajorAxisParam<U, K>` to guarantee transparent wrapper layout for FFI and zero-cost interop scenarios.
- Layout tests covering the new transparent-wrapper guarantees for cartesian and conic wrapper types.

### Changed
- README now documents the crate feature flags alongside the conic geometry guidance.

## [0.5.0 - 2026-03-27]

### Added
- `#[must_use]` on all constructors and pure transforms in `Rotation3`, `Translation3`, `Isometry3`, `Direction`.

### Changed
- `affn-derive` source split into `frame.rs` and `center.rs` submodules; `lib.rs` is now a thin entry-point (no user-visible API change).
- `cartesian/vector_serde.rs` and `cartesian/direction_serde.rs` merged into `cartesian/serde.rs` (no user-visible API change).
- `Rotation3` matrix multiply now uses `array::from_fn` instead of an indexed loop; removes the `#[allow(clippy::needless_range_loop)]` suppression.

### Fixed
- `Direction::new` doc clarified: `# Panics` section now references `try_new` as the fallible alternative.
- `Rotation3::from_matrix` doc updated with an explicit `# Preconditions` block describing the mathematical contract.
- `XYZ::magnitude_squared` doc explains why the return type is `f64` rather than `Quantity<U²>`.
- `classify_eccentricity_unchecked` doc explains the exact `e == 1.0` IEEE 754 boundary and its implications.
- `Direction` serde deserialization comment clarifies why `XYZ<f64>` is correct (directions are dimensionless).
- New `affn::conic` module for domain-agnostic conic geometry, including `ConicKind`, `ConicValidationError`, `ConicShape`, and kind markers `Elliptic`, `Parabolic`, and `Hyperbolic`.
- New validated conic parameterizations: erased forms `PeriapsisParam` and `SemiMajorAxisParam`, classification enums `ClassifiedPeriapsisParam` and `ClassifiedSemiMajorAxisParam`, typed wrappers `TypedPeriapsisParam` and `TypedSemiMajorAxisParam`, frame-tagged `ConicOrientation<F>`, and `OrientedConic<S, F>` aliases for common elliptic, parabolic, and hyperbolic combinations.
- Conversions between periapsis-distance and semi-major-axis conic forms, preserving eccentricity and preserving frame-tagged orientation on `OrientedConic`.
- `serde` support for conic shapes, orientations, and oriented conics under the existing `serde` feature, with round-trip coverage in the test suite.
- New `conic_showcase` example and expanded README guidance for the conic geometry layer.

### Changed
- Crate-level exports and `affn::prelude` now re-export the public conic geometry types.

## [0.4.1 - 2026-03-08]

### Added
- New astronomical frames behind the `astro` feature:
  - `EME2000`
  - `FK4B1950`
  - `TEME`
  - `MercuryFixed`
  - `VenusFixed`
  - `MarsFixed`
  - `MoonPrincipalAxes`
  - `JupiterSystemIII`
  - `SaturnFixed`
  - `UranusFixed`
  - `NeptuneFixed`
  - `PlutoFixed`
- Zero-cost `reinterpret_frame::<F2>()` helpers on Cartesian `Position`, `Vector`, and `Direction` for retagging values after an explicit transform.

## [0.3.3 - 2026-02-26]

### Added
- Custom format in display trait.

### Changed
- Changed the serialized field names from lon and lat to lon_deg and lat_deg.


## [0.3.2 - 2026-02-19]

### Fixed
- Published compatibility update for geodetic frames by pinning `affn-derive = 0.1.3`, ensuring `#[frame(ellipsoid = "...")]` generates `HasEllipsoid` implementations in downstream builds.

## [0.3.1 - 2026-02-19]

### Added
- New astronomical frames in `affn::frames::astro`: `GCRS`, `CIRS`, and `TIRS`.
- New ellipsoid API in `affn::ellipsoid`: `Ellipsoid`, `HasEllipsoid`, and predefined ellipsoids `Wgs84` and `Grs80`.
- New `affn::ellipsoidal` module with `ellipsoidal::Position<C, F, U>` for geodetic coordinates (`lon`, `lat`, `height`).
- Ellipsoid-aware geodetic conversions on `ellipsoidal::Position`: `to_cartesian` and `from_cartesian` (available when `F: HasEllipsoid`).
- Serde support for `ellipsoidal::Position`, preserving `lon`/`lat`/`height` payload compatibility.
- `#[frame(ellipsoid = "...")]` support in `affn-derive` to auto-implement `HasEllipsoid`.
- Geodetic frame-ellipsoid associations for built-in terrestrial frames: `ITRF` (`Grs80`) and `ECEF` (`Wgs84`).

### Changed
- Rotation constructors now use typed angles (`qtty::Radians`) in public APIs: `Rotation3::from_axis_angle`, `Rotation3::from_euler_xyz`, and `Rotation3::from_euler_zxz`.
- Added typed-axis helpers `Rotation3::rx`, `Rotation3::ry`, and `Rotation3::rz`; internal scalar axis-rotation builders are no longer public.
- Public exports and prelude now include ellipsoidal and ellipsoid types: `EllipsoidalPosition`, `Ellipsoid`, `HasEllipsoid`, `Wgs84`, and `Grs80`.

### Removed
- Removed the `geodesy` cargo feature and the legacy `geodesy::GeodeticCoord` type/module.

## [0.3.0 - 2026-02-12]

### Added
- Optional `astro` cargo feature with built-in astronomical frames in `affn::frames`: `ICRS`, `ICRF`, `EquatorialMeanJ2000`, `EquatorialMeanOfDate`, `EquatorialTrueOfDate`, `Horizontal`, `Ecliptic`, `ITRF`, `ECEF`, and `Galactic`.
- Feature-gated prelude re-exports for astronomical frames under `affn::prelude` (enabled with `astro`).
- `#[frame(inherent)]` support in `affn-derive` for generating frame-specific inherent constructors/accessors on `spherical::Direction` and `spherical::Position`.
- Shared spherical angular-separation helper using the numerically stable Vincenty formulation.
- `CenterParamsMismatchError` for operations on `Position` values with mismatched center runtime parameters.
- Checked `Position` operations that return errors instead of panicking on center-parameter mismatch: `try_distance_to` and `checked_sub`.
- Unit conversion helpers on Cartesian types: `Position::to_unit` and `Vector::to_unit`.

### Changed
- `spherical::Direction` and related call sites now use raw constructors (`new_raw`) in core APIs; canonicalization is handled by frame-specific generated constructors when available.
- Cartesian-to-spherical direction conversion now performs explicit azimuth normalization before raw construction.
- `frames` module layout was refactored to `src/frames/mod.rs` with feature-gated astronomical frame exports.
- `Position::distance_to` and `Position - Position` now enforce center-parameter compatibility in all builds (panic on mismatch, not debug-only).

### Removed
- Generic `spherical::Direction::ra()` and `spherical::Direction::dec()` aliases from the frame-agnostic direction type.
- Internal angle canonicalization helper functions in `spherical::direction`.

## [0.2.1 - 2026-02-09]

### Added
- `std::ops::Mul` overloads for `Rotation3`, `Translation3`, and `Isometry3` with raw array operands (`[f64; 3]`).
- Unit-aware `std::ops::Mul` overloads for affine operators using `[Quantity<U>; 3]` and `XYZ<Quantity<U>>`, preserving units through transforms.
- New operator-focused tests covering `Mul` behavior for raw arrays and `Quantity`-based operands.

## [0.2.0]

### Added
- New `affn-derive` proc-macro crate providing `#[derive(ReferenceFrame)]` and `#[derive(ReferenceCenter)]` (re-exported via `affn::prelude`).
- `ops` module with domain-agnostic affine operators: `Rotation3`, `Translation3`, and `Isometry3`.
- Cartesian line-of-sight helpers: `line_of_sight`, `line_of_sight_with_distance`, and `try_line_of_sight`.
- Cartesian ↔ spherical conversions for positions/directions (`to_spherical`, `from_spherical`), plus roundtrip example.
- More examples under `examples/` (basic cartesian algebra, parameterized centers, spherical roundtrip).
- GitHub Actions CI (`check`, `fmt`, `clippy`, `test`, `doctest`, `coverage`) and a local runner script (`ci-local.sh`).
- Integration tests for derive macros and expanded unit tests for cartesian/spherical types and formatting.

### Changed
- Crate is now fully domain-agnostic: concrete frames/centers are expected to live in downstream crates.
- `ReferenceCenter` and `ReferenceFrame` now require `Copy + Clone + Debug`; center runtime parameters are carried via `ReferenceCenter::Params`.
- `Position<C, F, U>` stores `C::Params` inline and adds `new_with_params` (plus convenience `new` for `Params = ()` centers).
- Public API reorganized with crate-level re-exports and a `prelude` for common imports (types, traits, derives, and operators).
- Version bumped from `0.1.0` to `0.2.0` and `Cargo.lock` updated to include `affn-derive`.

### Deprecated

### Removed
- Predefined astronomy-specific frames and centers (e.g., `ICRS`, `Ecliptic`, `Heliocentric`, `Geocentric`, `Topocentric`) from the core crate.
- `ObserverSite` and related astronomy-specific center parameter types from the core crate.

### Fixed
- Small performance improvements in affine operator hot paths (e.g., negation and loop-level optimizations).

### Security

## [0.1.0]

### Added
- Initial release (`mini-release`, commit `32695590db4480d0e3ce7c6e59c0e3a7a7ff3703`).
