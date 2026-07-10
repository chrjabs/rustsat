//! # SAT-Related Algorithms
//!
//! This module contains implementations of algorithms that build on top of SAT solvers.
//! The implementations here are typically intended to be relatively simple and are not optimized
//! for maximum performance.

#[cfg(feature = "optimization")]
pub mod maxsat;
