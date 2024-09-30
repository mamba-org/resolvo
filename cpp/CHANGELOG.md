# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.0](https://github.com/mamba-org/resolvo/releases/tag/resolvo_cpp-v0.2.0) - 2024-06-11

### Added
- More tracing ([#55](https://github.com/mamba-org/resolvo/pull/55))
- (**breaking**) Version set unions as solvable requirements ([#56](https://github.com/mamba-org/resolvo/pull/56))
- (**breaking**) Solve for optional solvables in addition to the root solvable ([#54](https://github.com/mamba-org/resolvo/pull/54))
- (**breaking**) Add `Problem` struct ([#62](https://github.com/mamba-org/resolvo/pull/62))
- (**breaking**) Decide on explicit requirements first ([#61](https://github.com/mamba-org/resolvo/pull/61))

### Fixed
- Display_merged_solvables to display merged solvables correctly ([#48](https://github.com/mamba-org/resolvo/pull/48))
- Add a virtual destructor to `DependencyProvider` ([#50](https://github.com/mamba-org/resolvo/pull/50))
- Fix off-by-one error in `Mapping::serialize` ([#58](https://github.com/mamba-org/resolvo/pull/58))

### Performance
* Visit less clauses during propagation ([#66](https://github.com/mamba-org/resolvo/pull/66))
* Implement a form of VSIDS ([#67](https://github.com/mamba-org/resolvo/pull/67))

## [0.1.0](https://github.com/mamba-org/resolvo/releases/tag/resolvo_cpp-v0.1.0) - 2024-06-11

### Added
- c++ bindings ([#41](https://github.com/mamba-org/resolvo/pull/41))
