[![Check & Test](https://github.com/chrjabs/rustsat/actions/workflows/cadical.yml/badge.svg)](https://github.com/chrjabs/rustsat/actions/workflows/cadical.yml)
[![crates.io](https://img.shields.io/crates/v/rustsat-cadical)](https://crates.io/crates/rustsat-cadical)
[![docs.rs](https://img.shields.io/docsrs/rustsat-cadical)](https://docs.rs/rustsat-cadical)
[![License](https://img.shields.io/crates/l/rustsat-cadical)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-cadical - Interface to the CaDiCaL SAT Solver for RustSAT

Armin Biere's SAT solver [CaDiCaL](https://github.com/arminbiere/cadical) to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

**Note**: at the moment this crate is known to not work on Windows since CaDiCaL is non-trivial to get to work on Windows.

## Features

- `debug`: if this feature is enables, the C++ library will be built with debug and check functionality if the Rust project is built in debug mode
- `safe`: disable writing through 'popen' for more safe usage of the library in applications
- `quiet`: exclude message and profiling code (logging too)
- `logging`: include logging code (but disabled by default)

## CaDiCaL Versions

CaDiCaL versions can be selected via cargo crate features.
All CaDiCaL versions up to [Version 2.1.0](https://github.com/arminbiere/cadical/releases/tag/rel-2.0.0) are available.
For the full list of versions and the changelog see [the CaDiCaL releases](https://github.com/arminbiere/cadical/releases).

Without any features selected, the newest version will be used.
If conflicting CaDiCaL versions are requested, the newest requested version will be selected.

## Customization

In order to build a custom version of CaDiCaL, this crate supports two environment variables to
customize the C++ source code that CaDiCaL is built from.

- `CADICAL_PATCHES` allows to specify a list of colon-separated paths to patch files that will
    be applied to the CaDiCaL source repository before building it. These patches are applied
    in order of appearance _after_ the patches of this crate have been applied.
- `CADICAL_SRC_DIR` allows for overriding where the C++ library is built from. By default this
    crate fetches the appropriate code from [the GitHub
    repo](https://github.com/arminbiere/cadical). If this variable is set, the directory specified
    there is used instead. Note that when using this variable, the crate will not apply any
    patches, the user is responsible for applying the appropriate and necessary patches from the
    [`patches/`](https://github.com/chrjabs/rustsat/tree/main/cadical/patches) directory.

<!-- cargo-rdme end -->
