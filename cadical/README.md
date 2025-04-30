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
[Version 2.1.3](https://github.com/arminbiere/cadical/releases/tag/rel-2.1.3)
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
