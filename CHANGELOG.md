# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- New astronomical frames in `affn::frames::astro`: `GCRS`, `CIRS`, and `TIRS`.
- New geodetic frames
### Changed
- Rotation constructors now use typed angles (`qtty::Radians`) in public APIs: `Rotation3::from_axis_angle`, `Rotation3::from_euler_xyz`, and `Rotation3::from_euler_zxz`.
- Added typed-axis helpers `Rotation3::rx`, `Rotation3::ry`, and `Rotation3::rz`; internal scalar axis-rotation builders are no longer public.

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
