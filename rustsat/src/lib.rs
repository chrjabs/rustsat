#![doc = include_str!("../../README.md")]
#![cfg_attr(feature = "bench", feature(test))]

pub mod encodings;
pub mod instances;
pub mod solvers;
pub mod types;

pub mod capi;

pub mod utils;

#[cfg(feature = "bench")]
#[cfg(test)]
mod bench;
