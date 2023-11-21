#![doc = include_str!("../README.md")]
#![cfg_attr(feature = "bench", feature(test))]

pub mod encodings;
pub mod instances;
pub mod solvers;
pub mod types;

mod capi;
#[cfg(feature = "pyapi")]
pub mod pyapi;

pub mod utils;

#[cfg(feature = "bench")]
#[cfg(test)]
mod bench;
