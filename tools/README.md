# rustsat-tools - Tools and Unittests for the RustSAT Library

This crate contains tools and unit tests for the RustSAT library.
Unittests are here because they depend on solver interface crates, which in turn depend on RustSAT, which creates a dependency cycle if the tests are in RustSAT directly.
