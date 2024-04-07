# Migration Guide for Breaking Changes in v0.5.0

This document gives an overview of the breaking API changes in v0.5.0 and how
to update your code accordingly. Mostly, follow the error messages the compiler
will give you after updating to the new RustSAT version.

## Error Handling

Error handling in the `Solve` trait, and file parsers now uses the
[`anyhow`](https://docs.rs/anyhow/latest/anyhow/) crate. This allows for better
error messages, and better tracing. In the process, some of the error types or
variants that are not needed any more have been removed:

- `rustsat::solvers::SolverError` has been removed and only
  `rustsat::solvers::StateError` remains
- `rustsat::instances::fio::opb::Error` has been removed
- `rustsat::instances::fio::dimacs::Error` has been removed
- `rustsat::instances::fio::ParsingError` has been removed
- `rustsat::solvers::SolverState::Error` has also been removed as no error
  state is needed with proper error returns

If you need to handle a specific error, you can use `anyhow`'s
[`downcast`](https://docs.rs/anyhow/latest/anyhow/struct.Error.html#method.downcast)
(e.g., on `solvers::StateError`), but I imagine most often these errors are
anyhow just propagated outwards and displayed.

## Changes to Improve API Ergonomics

There have been some API changes to improve usability, even though they are breaking.

- File writing methods: all file writing methods (on `SatInstance`,
  `OptInstance` and `MultiOptInstance`) are now called `write_` instead of `to_`.
  Furthermore they take references instead of values and will return an error if
  a specific format of the instance is expected but the instance does not satisfy
  this requirement.
- File reading methods: all file reading methods (DIMACS and OPB, on
  `SatInsatnce`, etc) now require a `BufRead` type as input. Previously, the
  reader was internally wrapped in a
  [`BufReader`](https://doc.rust-lang.org/stable/std/io/struct.BufReader.html)
  object. This now has to be done externally to avoid potentially double
  buffering.
- "Heavy" conversion function (e.g., `SatInstance::to_cnf`) are now called
  `into_`. Additionally, inplace converter functions named `convert_to_` are also
  provided.
- Methods providing references to internal data are now named `_ref` and `_mut`
  if mutability is allowed. If only a non-mutable accessor is present, the `_ref`
  suffix is omitted (e.g., for `SatInstance::cnf`).
