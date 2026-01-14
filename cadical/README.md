[![crates.io](https://img.shields.io/crates/v/rustsat-cadical?style=for-the-badge&logo=rust)](https://crates.io/crates/rustsat-cadical)
[![docs.rs](https://img.shields.io/docsrs/rustsat-cadical?style=for-the-badge&logo=docsdotrs)](https://docs.rs/rustsat-cadical)
[![License](https://img.shields.io/crates/l/rustsat-cadical?style=for-the-badge)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-cadical - Interface to the CaDiCaL SAT Solver for RustSAT

Armin Biere's SAT solver [CaDiCaL](https://github.com/arminbiere/cadical) to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

**Note**: at the moment this crate is known to not work on Windows since CaDiCaL is non-trivial to get to work on Windows.

## Features

- `debug`: if this feature is enabled, the Cpp library will be built with debug and check
  functionality if the Rust project is built in debug mode. API tracing via the
  `CADICAL_API_TRACE` environment variable is also enabled in debug mode.
- `safe`: disable writing through `popen` for more safe usage of the library in applications
- `quiet`: exclude message and profiling code (logging too)
- `logging`: include logging code (but disabled by default)
- `tracing`: always include CaDiCaL API tracing via the `CADICAL_API_TRACE` environment
  variable and the [`CaDiCaL::trace_api_calls`] method

## CaDiCaL Versions

CaDiCaL versions can be selected via cargo crate features.
All CaDiCaL versions from
[Version 1.5.0](https://github.com/arminbiere/cadical/releases/tag/rel-1.5.0)
up to
[Version 2.2.1](https://github.com/arminbiere/cadical/releases/tag/rel-2.2.1)
are available. For the full list of versions and the changelog see
[the CaDiCaL releases](https://github.com/arminbiere/cadical/releases).

Without any features selected, the newest version will be used.
If conflicting CaDiCaL versions are requested, the newest requested version will be selected.

If the determined version is _not_ the newest available, and no custom source directory is
specified (see customization below), the CaDiCaL source code is downloaded at compile time,
which requires network access.

## Customization

In order to build a custom version of CaDiCaL, this crate supports two environment variables to
customize the Cpp source code that CaDiCaL is built from.

- `CADICAL_PATCHES` allows to specify a list of colon-separated paths to patch files that will
  be applied to the CaDiCaL source repository before building it. These patches are applied
  in order of appearance _after_ the patches of this crate have been applied.
- `CADICAL_SRC_DIR` allows for overriding where the Cpp library is built from. By default this
  crate fetches the appropriate code from [the GitHub
  repository](https://github.com/arminbiere/cadical). If this variable is set, the directory specified
  there is used instead. Note that when using this variable, the crate will not apply any
  patches, the user is responsible for applying the appropriate and necessary patches from the
  [`patches/`](https://github.com/chrjabs/rustsat/tree/main/cadical/patches) directory.

## Cpp Compiler Features

By default, the build script of this crate uses the same compiler/platform tests as CaDiCaL's
`configure` script to detect whether certain Cpp compiler features are available.
The following environment variables allow for manually modifying the logic for detecting
compiler features.

- `CADICAL_RUN_COMPILER_TESTS`: By default we only consider a compiler feature available if the
  test compiles _and runs_.
  With this environment variable set to `0` or `false` a feature is considered available if the
  test compiles correctly, without trying to execute it.
  This is useful for cross-compilation settings where executing the compiled binary is not
  possible.
- `CADICAL_FLEXIBLE_ARRAY_MEMBERS` enables (`1` or `true`) or disables (`0` or `false`) or
  automatically checks (`auto`) the availability of the flexible array members compiler
  feature.
  Disabling the feature is equivalent to `--no-flexible` in CaDiCaL's `configure` script.
- `CADICAL_CLOSEFROM` marks `closefrom` as available (`1` or `true`) or unavailable (`0` or
  `false`) or automatically checks (`auto`) the availability.
  Disabling the feature is equivalent to `--no-closefrom` in CaDiCaL's `configure` script.
- `CADICAL_UNLOCKED_IO` enables (`1` or `true`) or disables (`0` or `false`) or automatically
  checks (`auto`) the availability of the unlocked IO platform feature.
  Disabling the feature is equivalent to `--no-unlocked` in CaDiCaL's `configure` script.

By default, the availability of all compiler/platform features is automatically checked.

## Minimum Supported Rust Version (MSRV)

Currently, the MSRV is 1.77.0, the plan is to always support an MSRV that is at least a year
old.

Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
sure to pin a precise version of RustSAT.

Note that the specified minimum-supported Rust version only applies if the _newest_ version of
CaDiCaL is build.
Older versions are pulled down via the [`git2`](https://crates.io/crates/git2) crate, which has
transitive dependencies that have a higher MSRV.

<!-- cargo-rdme end -->
