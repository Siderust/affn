# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

### Changed

### Deprecated

### Removed

### Fixed

### Security

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
