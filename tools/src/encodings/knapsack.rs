//! # Shared Knapsack Encoding Tooling
//!
//! - Data types
//! - Input parser
//! - Random generator

use std::{io, ops::Range};

use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

/// An instance of the (multi-criteria 0-1) knapsack problem
#[derive(Clone, PartialEq, Eq)]
pub struct Knapsack {
    pub(crate) items: Vec<ItemData>,
    pub(crate) capacity: usize,
}

/// Data associated with one knapsack item
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct ItemData {
    pub weight: usize,
    pub values: Vec<usize>,
}

pub enum Capacity {
    /// A fixed knapsack capacity
    Fixed(usize),
    /// Calculate the capacity as the total weight divided by the given value
    FractionTotalWeight(usize),
}

impl Knapsack {
    pub fn random(
        n_items: usize,
        n_objectives: usize,
        value_range: Range<usize>,
        weight_range: Range<usize>,
        capacity: Capacity,
        seed: u64,
    ) -> Self {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let items: Vec<_> = (0..n_items)
            .map(|_| {
                let weight = rng.random_range(weight_range.clone());
                let values = (0..n_objectives)
                    .map(|_| rng.random_range(value_range.clone()))
                    .collect();
                ItemData { weight, values }
            })
            .collect();
        let capacity = match capacity {
            Capacity::Fixed(cap) => cap,
            Capacity::FractionTotalWeight(div) => {
                items.iter().fold(0, |sum, item| sum + item.weight) / div
            }
        };
        Self { items, capacity }
    }

    pub fn from_file(reader: impl io::BufRead, format: FileFormat) -> anyhow::Result<Self> {
        match format {
            FileFormat::MooLibrary => parsing::parse_moolib(reader),
            FileFormat::VOptLib => parsing::parse_voptlib(reader),
        }
    }
}

/// Possible Knapsack input file formats
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FileFormat {
    /// Input files as provided by [MOO-Library](http://home.ku.edu.tr/~moolibrary/)
    MooLibrary,
    /// Input files as provided by [vOptLib](https://github.com/vOptSolver/vOptLib/tree/master/UKP)
    VOptLib,
}

mod parsing {
    use std::io;

    use anyhow::Context;
    use nom::{
        bytes::complete::tag,
        character::complete::{space0, u32},
        error::Error as NomErr,
        sequence::tuple,
    };

    use crate::parsing::{callback_list, single_value};

    macro_rules! next_non_comment_line {
        ($reader:expr) => {
            'block: {
                let mut buf = String::new();
                while $reader.read_line(&mut buf)? > 0 {
                    if !buf.trim_start().starts_with('#') && !buf.trim().is_empty() {
                        break 'block Some(buf);
                    }
                    buf.clear();
                }
                None
            }
        };
    }

    pub fn parse_moolib(mut reader: impl io::BufRead) -> anyhow::Result<super::Knapsack> {
        let line = next_non_comment_line!(reader)
            .context("file ended before number of objectives line")?;
        let (_, n_obj) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of objectives line '{line}'"))?;
        let line =
            next_non_comment_line!(reader).context("file ended before number of items line")?;
        let (_, n_items) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of items line '{line}'"))?;
        let line = next_non_comment_line!(reader).context("file ended before capacity line")?;
        let (_, capacity) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse capacity line '{line}'"))?;
        let mut inst = super::Knapsack {
            items: vec![
                super::ItemData {
                    weight: 0,
                    values: vec![]
                };
                n_items as usize
            ],
            capacity: capacity as usize,
        };
        let mut buf = String::new();
        let mut started = false;
        let mut ended = false;
        while reader.read_line(&mut buf)? > 0 {
            let remain = buf.trim_start();
            if remain.starts_with('#') || buf.trim().is_empty() {
                buf.clear();
                continue;
            }
            let remain = if started {
                remain
            } else {
                anyhow::ensure!(remain.starts_with('['), "expected list to start");
                started = true;
                &remain[1..]
            };
            let mut item_idx = 0;
            let remain = callback_list(remain, u32, |value| {
                anyhow::ensure!(item_idx < inst.items.len(), "too many values in value list");
                inst.items[item_idx].values.push(value as usize);
                item_idx += 1;
                Ok(())
            })?;
            match tuple::<_, _, NomErr<_>, _>((space0, tag(","), space0))(remain) {
                Ok(_) => (),
                Err(_) => {
                    tuple::<_, _, NomErr<_>, _>((space0, tag("]")))(remain)
                        .map_err(|e| e.to_owned())
                        .context("failed to find closing delimiter for value list")?;
                    ended = true;
                    break;
                }
            }
            buf.clear();
        }
        anyhow::ensure!(ended, "file ended before value list ended");
        let line = next_non_comment_line!(reader).context("file ended before weight line")?;
        let mut item_idx = 0;
        callback_list(line.trim_start(), u32, |weight| {
            anyhow::ensure!(
                item_idx < inst.items.len(),
                "too many values in weight list"
            );
            inst.items[item_idx].weight = weight as usize;
            item_idx += 1;
            Ok(())
        })?;
        for item in &inst.items {
            anyhow::ensure!(
                item.values.len() == n_obj as usize,
                "number of values for item does not match number of objectives"
            );
        }
        Ok(inst)
    }

    pub fn parse_voptlib(mut reader: impl io::BufRead) -> anyhow::Result<super::Knapsack> {
        let line =
            next_non_comment_line!(reader).context("file ended before number of items line")?;
        let (_, n_items) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of items line '{line}'"))?;
        let line = next_non_comment_line!(reader)
            .context("file ended before number of objectives line")?;
        let (_, n_obj) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of objectives line '{line}'"))?;
        let _ = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of constraints line '{line}'"))?;
        let mut inst = super::Knapsack {
            items: vec![
                super::ItemData {
                    weight: 0,
                    values: vec![]
                };
                n_items as usize
            ],
            capacity: 0,
        };
        for obj_idx in 0..n_obj {
            for item_idx in 0..n_items {
                let line = next_non_comment_line!(reader).with_context(|| {
                    format!("file ended before {item_idx} value of objective {obj_idx}")
                })?;
                let (_, value) = single_value(u32, "#")(&line)
                    .map_err(|e| e.to_owned())
                    .with_context(|| {
                        format!("failed to parse {item_idx} value of objective {obj_idx} '{line}'")
                    })?;
                inst.items[item_idx as usize].values.push(value as usize);
            }
        }
        for item_idx in 0..n_items {
            let line = next_non_comment_line!(reader)
                .with_context(|| format!("file ended before weight of item {item_idx}"))?;
            let (_, weight) = single_value(u32, "#")(&line)
                .map_err(|e| e.to_owned())
                .with_context(|| format!("failed to parse weight of item {item_idx} '{line}'"))?;
            inst.items[item_idx as usize].weight = weight as usize;
        }
        Ok(inst)
    }

    #[cfg(test)]
    mod tests {
        use std::{fs::File, io::BufReader};

        #[test]
        fn moolib() {
            let reader = BufReader::new(File::open("./data/KP_p-3_n-10_ins-1.dat").unwrap());
            super::parse_moolib(reader).unwrap();
        }

        #[test]
        fn voptlib() {
            let reader = BufReader::new(File::open("./data/F5050W01.dat").unwrap());
            super::parse_voptlib(reader).unwrap();
        }
    }
}
