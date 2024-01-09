# rustsat-cadical - Interface to the CaDiCaL SAT Solver for RustSAT

Armin Biere's SAT solver [CaDiCaL](https://github.com/arminbiere/cadical) to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

## Features

- `debug`: if this feature is enables, the C++ library will be built with debug and check functionality if the Rust project is built in debug mode
- `safe`: disable writing through 'popen' for more safe usage of the library in applications
- `quiet`: exclude message and profiling code (logging too)
- `logging`: include logging code (but disabled by default)

## CaDiCaL Versions

CaDiCaL versions can be selected via cargo crate features.
All CaDiCaL versions up to [Version 1.9.4](https://github.com/arminbiere/cadical/releases/tag/rel-1.9.4) are available.
For the full list of versions and the changelog see [the CaDiCaL releases](https://github.com/arminbiere/cadical/releases).

Without any features selected, the newest version will be used.
If conflicting CaDiCaL versions are requested, the newest requested version will be selected.