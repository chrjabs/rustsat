# Glucose 4

The original sources are pulled from [here](https://www.labri.fr/perso/lsimon/research/glucose/#glucose-4.2.1).
This repository extends Glucose 4 with a C API and is used in RustSAT.

## Directory overview:

- `mtl/`: Minisat Template Library
- `core/`: A core version of the solver glucose (no main here)
- `simp/`: An extended solver with simplification capabilities
- `parallel/`: A multicore version of glucose

## To build (release version: without assertions, statically linked, etc):

Like minisat....

```
cd { simp | parallel }
make rs
```

## Usage:

In simp directory: `./glucose --help`

In parallel directory: `./glucose-syrup --help`
