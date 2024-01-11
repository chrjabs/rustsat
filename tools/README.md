[![Check & Test](https://github.com/chrjabs/rustsat/actions/workflows/check-test.yml/badge.svg)](https://github.com/chrjabs/rustsat/actions/workflows/check-test.yml)
[![crates.io](https://img.shields.io/crates/v/rustsat-tools)](https://crates.io/crates/rustsat-tools)
[![docs.rs](https://img.shields.io/docsrs/rustsat-tools)](https://docs.rs/rustsat-tools)
[![License](https://img.shields.io/crates/l/rustsat-tools)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-tools - Tools and Unittests for the RustSAT Library

This crate contains tools and unit tests for the RustSAT library.
Unittests are here because they depend on solver interface crates, which in turn depend on RustSAT, which creates a dependency cycle if the tests are in RustSAT directly.

<!-- cargo-rdme end -->
