# Changelog

## `0.0.6`

- `FF` improved public api
- `FM` module
  - added `epoch` ids for every writes
  - added `wait_for_durability` to enable waiting for durability
- improved test coverage (80+ tests)

## `0.0.5`

- improved error propogation
- all modules are behind feature flags (all available by default)
- failed attempt to go `no_std`

## `0.0.4`

- `FF` module
  - Yanked `read` & `write` ops
  - Migrated io ops to use `iovecs` for linux impl
  - (Rename) `FF` -> `FrozenFile`
  - Added `mac` support
- `FM` module
  - (Rename) `FM` -> `FrozenMMap`
  - Added `mac` support

## `0.0.3`

- Improved `docs`
- Added `examples/`

## `0.0.2`

- Improved `FFCfg` & `FMCfg` w/ builder pattern construction

## `0.0.1`

- Impl of `fe` (Frozen Error) for custom error repr
- Impl of `hints` module for compiler/branching hints
- Impl of `ff` (FrozenFile) w/ `Linux` (x86 & aarch64)
- Impl of `fm` (FrozenMMAp) w/ `Linux` (x86 & aarch64)
