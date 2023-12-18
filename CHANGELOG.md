# Changelog

All notable changes to this project will be documented in this file.

## [0.4.0] - 2023-12-18

### Bug Fixes

- Set var manager in SatInstance::from_iter
- Set vm correctly in SatInstance::from(Cnf)
- Coarse convergence bounds
- Link capi tests to archive libs
- Typo in capi
- Parse empty instances correctly
- Limited connections in node db
- Next value in db-referencing gtes

### Documentation

- (limited) python api documentation

### Features

- Python api expose lit, clause, cnf
- Python len and indexing support for clause and cnf
- Feature switch for python api
- Python iterators
- Totalizer and comparison operators in pyapi
- Expose all encodings in python api
- Extend internal node api
- Limited connections in node db
- Constant method for objective
- Allow cloning totalizer db

## [0.3.0]

### Refactor

- Allow encodings to output straight to solvers

### Features

- Alternative totalizer implementation based on a totalizer database
- Dynamic polynomial watchdog encoing
- Changes to public API: changed some vectores to slices
- Changed internal variable/literal representation from `usize` to `u32`

## [0.2.x]

Solver interfaces factored out into seperate crates.
See detailed changes in [GitHub Releases](https://github.com/chrjabs/rustsat/releases).

## [0.1.2]

Updated initial version with working dependencies.

## [0.1.0] and [0.1.1]

Yanked because of dependencies that don't exist anymore
