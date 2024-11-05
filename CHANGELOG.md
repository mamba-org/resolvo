# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.8.4](https://github.com/mamba-org/resolvo/compare/resolvo-v0.8.3...resolvo-v0.8.4) - 2024-11-05

### Fixed

- constraint formatting ([#80](https://github.com/mamba-org/resolvo/pull/80))

## [0.8.3](https://github.com/mamba-org/resolvo/compare/resolvo-v0.8.2...resolvo-v0.8.3) - 2024-11-01

### Fixed

- constraint at root can conflict ([#79](https://github.com/mamba-org/resolvo/pull/79))

### Other

- *(ci)* bump prefix-dev/rattler-build-action from 0.2.16 to 0.2.18 ([#78](https://github.com/mamba-org/resolvo/pull/78))
- *(ci)* bump prefix-dev/rattler-build-action from 0.2.15 to 0.2.16 ([#75](https://github.com/mamba-org/resolvo/pull/75))

## [0.8.2](https://github.com/mamba-org/resolvo/compare/resolvo-v0.8.1...resolvo-v0.8.2) - 2024-10-04

### Fixed

- add missing ord trait for NameId ([#73](https://github.com/mamba-org/resolvo/pull/73))

### Other

- *(ci)* bump prefix-dev/rattler-build-action from 0.2.14 to 0.2.15 ([#71](https://github.com/mamba-org/resolvo/pull/71))
- prepare cpp v0.2.0 ([#69](https://github.com/mamba-org/resolvo/pull/69))

## [0.8.1](https://github.com/mamba-org/resolvo/compare/resolvo-v0.8.0...resolvo-v0.8.1) - 2024-09-30

### Other

- implement a form of VSIDS ([#67](https://github.com/mamba-org/resolvo/pull/67))
- *(ci)* bump prefix-dev/rattler-build-action from 0.2.13 to 0.2.14 ([#65](https://github.com/mamba-org/resolvo/pull/65))
- visit fewer clauses during propagation ([#66](https://github.com/mamba-org/resolvo/pull/66))

## [0.8.0](https://github.com/mamba-org/resolvo/compare/resolvo-v0.7.0...resolvo-v0.8.0) - 2024-09-09

### Added

- [**breaking**] decide on explicit requirements first ([#61](https://github.com/mamba-org/resolvo/pull/61))
- add better timing notebook and measuring ([#64](https://github.com/mamba-org/resolvo/pull/64))
- *(solver)* [**breaking**] Make `Problem` use builder pattern ([#62](https://github.com/mamba-org/resolvo/pull/62))

## [0.7.0](https://github.com/mamba-org/resolvo/compare/resolvo-v0.6.2...resolvo-v0.7.0) - 2024-08-06

### Added
- *(solver)* [**breaking**] Solve for optional solvables in addition to the root solvable ([#54](https://github.com/mamba-org/resolvo/pull/54))
- [**breaking**] Version set unions as solvable requirements ([#56](https://github.com/mamba-org/resolvo/pull/56))

### Fixed
- Fix off-by-one error in `Mapping::serialize` ([#58](https://github.com/mamba-org/resolvo/pull/58))

### Other
- *(ci)* bump prefix-dev/rattler-build-action from 0.2.12 to 0.2.13 ([#59](https://github.com/mamba-org/resolvo/pull/59))
- *(ci)* bump prefix-dev/rattler-build-action from 0.2.11 to 0.2.12 ([#57](https://github.com/mamba-org/resolvo/pull/57))
- Add more tracing ([#55](https://github.com/mamba-org/resolvo/pull/55))
- *(ci)* bump prefix-dev/rattler-build-action from 0.2.10 to 0.2.11 ([#53](https://github.com/mamba-org/resolvo/pull/53))
- *(ci)* bump prefix-dev/rattler-build-action from 0.2.9 to 0.2.10 ([#51](https://github.com/mamba-org/resolvo/pull/51))

## [0.6.2](https://github.com/mamba-org/resolvo/compare/resolvo-v0.6.1...resolvo-v0.6.2) - 2024-06-11

### Added
- release-plz resolvo_cpp
- add rattler-build recipe ([#47](https://github.com/mamba-org/resolvo/pull/47))
- c++ bindings ([#41](https://github.com/mamba-org/resolvo/pull/41))

## [0.6.1](https://github.com/mamba-org/resolvo/compare/resolvo-v0.6.0...resolvo-v0.6.1) - 2024-06-10

### Added
- add `DependencySnapshot` ([#44](https://github.com/mamba-org/resolvo/pull/44))

### Fixed
- publish state of tool

## [0.6.0](https://github.com/mamba-org/resolvo/compare/v0.5.0...v0.6.0) - 2024-06-07

### Other
- remove `Pool` from API ([#40](https://github.com/mamba-org/resolvo/pull/40))

## [0.5.0](https://github.com/mamba-org/resolvo/compare/v0.4.1...v0.5.0) - 2024-06-03

### Added
- root constraints ([#38](https://github.com/mamba-org/resolvo/pull/38))

### Other
- small memory performance optimizations ([#35](https://github.com/mamba-org/resolvo/pull/35))

## [0.4.1](https://github.com/mamba-org/resolvo/compare/v0.4.0...v0.4.1) - 2024-05-22

### Added
- add release-plz ([#32](https://github.com/mamba-org/resolvo/pull/32))

### Fixed
- relax ord constraint ([#31](https://github.com/mamba-org/resolvo/pull/31))

### Other
- dependencies ([#33](https://github.com/mamba-org/resolvo/pull/33))
- add projects using resolvo
