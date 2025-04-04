[![crates.io](https://img.shields.io/crates/v/rustsat-kissat?style=for-the-badge)](https://crates.io/crates/rustsat-kissat)
[![docs.rs](https://img.shields.io/docsrs/rustsat-kissat?style=for-the-badge)](https://docs.rs/rustsat-kissat)
[![License](https://img.shields.io/crates/l/rustsat-kissat?style=for-the-badge)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-kissat - Interface to the Kissat SAT Solver for RustSAT

Armin Biere's SAT solver [Kissat](https://github.com/arminbiere/kissat) to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

**Note**: at the moment this crate is known to not work on Windows since Kissat is non-trivial to get to work on Windows.

## Features

- `debug`: if this feature is enables, the C library will be built with debug functionality if the Rust project is built in debug mode
- `safe`: disable writing through `popen` for more safe usage of the library in applications
- `quiet`: exclude message and profiling code (logging too)

## Kissat Versions

Kissat versions can be selected via cargo crate features.
The following Kissat versions are available:
- `v4-0-2`: [Version 4.0.2](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.2)
- `v4-0-1`: [Version 4.0.1](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.1)
- `v4-0-0`: [Version 4.0.0](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.0)
- `v3-1-0`: [Version 3.1.0](https://github.com/arminbiere/kissat/releases/tag/rel-3.1.0)
- `v3-0-0`: [Version 3.0.0](https://github.com/arminbiere/kissat/releases/tag/rel-3.0.0)
- `sc2022-light`: [SAT Competition 2022 Light](https://github.com/arminbiere/kissat/releases/tag/sc2022-light)
- `sc2022-hyper`: [SAT Competition 2022 Hyper](https://github.com/arminbiere/kissat/releases/tag/sc2022-hyper)
- `sc2022-bulky`: [SAT Competition 2022 Bulky](https://github.com/arminbiere/kissat/releases/tag/sc2022-bulky)

Without any features selected, the newest version will be used.
If conflicting Kissat versions are requested, the newest requested version will be selected.

If the determined version is _not_ the newest available, and no custom source directory is
specified (see customization below), the Kissat source code is downloaded at compile time,
which requires network access.

## Customization

In order to build a custom version of Kissat, this crate supports the `KISSAT_SRC_DIR`
environment variable.
If this is set, Kissat will be built from the path specified there.

<!-- cargo-rdme end -->
