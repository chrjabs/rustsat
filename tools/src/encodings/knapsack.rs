//! # Shared Knapsack Encoding Tooling
//!
//! - Data types
//! - Input parser
//! - Random generator

use std::{io, ops::Range};

use chacha20::ChaCha8Rng;
use rand::{RngExt, SeedableRng};

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
    use rustsat::{instances::fio::ParsingError, utils};
    use winnow::{
        ascii::{dec_uint, space0},
        error::{ContextError, StrContext, StrContextValue},
        token::rest,
        Parser,
    };

    use crate::parsing::{single_value, ListCallbackParser};

    macro_rules! next_non_comment_line {
        ($reader:expr, $lineno:expr) => {
            'block: {
                let mut buf = String::new();
                while $reader.read_line(&mut buf)? > 0 {
                    $lineno += 1;
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
        let mut line_num = 0;
        let line = next_non_comment_line!(reader, line_num)
            .context("file ended before number of objectives line")?;
        let n_obj = single_value(dec_uint::<_, usize, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "number of objectives",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        let line = next_non_comment_line!(reader, line_num)
            .context("file ended before number of items line")?;
        let n_items = single_value(dec_uint::<_, usize, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "number of items",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        let line =
            next_non_comment_line!(reader, line_num).context("file ended before capacity line")?;
        let capacity = single_value(dec_uint::<_, usize, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "capacity",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        let mut inst = super::Knapsack {
            items: vec![
                super::ItemData {
                    weight: 0,
                    values: vec![]
                };
                n_items
            ],
            capacity,
        };
        let mut buf = String::new();
        let mut started = false;
        let mut ended = false;
        while reader.read_line(&mut buf)? > 0 {
            line_num += 1;
            let remain = buf.trim();
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
            let (_, remain) = (
                ListCallbackParser::new(
                    |value| {
                        if item_idx >= inst.items.len() {
                            let mut err = ContextError::new();
                            err.push(StrContext::Expected(StrContextValue::Description(
                                "too many values",
                            )));
                            return Err(err);
                        }
                        inst.items[item_idx].values.push(value);
                        item_idx += 1;
                        Ok(())
                    },
                    dec_uint::<_, usize, ContextError>,
                )
                .context(StrContext::Expected(StrContextValue::Description(
                    "list of values",
                ))),
                rest,
            )
                .parse(remain)
                .map_err(|e| {
                    ParsingError::from_parse(
                        &e,
                        &buf,
                        utils::substr_offset(&buf, remain).unwrap(),
                        line_num,
                    )
                })?;
            match (space0::<_, ContextError>, ',').parse(remain) {
                Ok(_) => (),
                Err(_) => {
                    (space0::<_, ContextError>, ']')
                        .context(StrContext::Expected(StrContextValue::Description(
                            "list delimiter or end",
                        )))
                        .parse(remain)
                        .map_err(|e| {
                            ParsingError::from_parse(
                                &e,
                                &buf,
                                utils::substr_offset(&buf, remain).unwrap(),
                                line_num,
                            )
                        })?;
                    ended = true;
                    break;
                }
            }
            buf.clear();
        }
        anyhow::ensure!(ended, "file ended before value list ended");
        let line =
            next_non_comment_line!(reader, line_num).context("file ended before weight line")?;
        let mut item_idx = 0;
        ListCallbackParser::new(
            |value| {
                if item_idx >= inst.items.len() {
                    let mut err = ContextError::new();
                    err.push(StrContext::Expected(StrContextValue::Description(
                        "too many values",
                    )));
                    return Err(err);
                }
                inst.items[item_idx].weight = value;
                item_idx += 1;
                Ok(())
            },
            dec_uint::<_, usize, ContextError>,
        )
        .context(StrContext::Expected(StrContextValue::Description(
            "list of values",
        )))
        .parse(line.trim())
        .map_err(|e| {
            ParsingError::from_parse(
                &e,
                &line,
                utils::substr_offset(&line, line.trim_start()).unwrap(),
                line_num,
            )
        })?;
        for item in &inst.items {
            anyhow::ensure!(
                item.values.len() == n_obj,
                "number of values for item does not match number of objectives"
            );
        }
        Ok(inst)
    }

    pub fn parse_voptlib(mut reader: impl io::BufRead) -> anyhow::Result<super::Knapsack> {
        let mut line_num = 0;
        let line = next_non_comment_line!(reader, line_num)
            .context("file ended before number of items line")?;
        let n_items = single_value(dec_uint::<_, usize, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "number of items",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        let line = next_non_comment_line!(reader, line_num)
            .context("file ended before number of objectives line")?;
        let n_obj = single_value(dec_uint::<_, u32, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "number of objectives",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        single_value(dec_uint::<_, u32, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "number of constraints",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        let mut inst = super::Knapsack {
            items: vec![
                super::ItemData {
                    weight: 0,
                    values: vec![]
                };
                n_items
            ],
            capacity: 0,
        };
        for obj_idx in 0..n_obj {
            for item_idx in 0..n_items {
                let line = next_non_comment_line!(reader, line_num).with_context(|| {
                    format!("file ended before {item_idx} value of objective {obj_idx}")
                })?;
                let value = single_value(dec_uint::<_, usize, ContextError>, "#")
                    .context(StrContext::Expected(StrContextValue::Description(
                        "objective value",
                    )))
                    .parse(&line)
                    .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
                inst.items[item_idx].values.push(value);
            }
        }
        for item_idx in 0..n_items {
            let line = next_non_comment_line!(reader, line_num)
                .with_context(|| format!("file ended before weight of item {item_idx}"))?;
            let weight = single_value(dec_uint::<_, usize, ContextError>, "#")
                .context(StrContext::Expected(StrContextValue::Description("weight")))
                .parse(&line)
                .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
            inst.items[item_idx].weight = weight;
        }
        Ok(inst)
    }

    #[cfg(test)]
    mod tests {
        use std::{fs::File, io::BufReader};

        #[test]
        fn moolib() {
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let reader = BufReader::new(
                File::open(format!("{manifest}/data/KP_p-3_n-10_ins-1.dat")).unwrap(),
            );
            super::parse_moolib(reader).unwrap();
        }

        #[test]
        fn voptlib() {
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let reader =
                BufReader::new(File::open(format!("{manifest}/data/F5050W01.dat")).unwrap());
            super::parse_voptlib(reader).unwrap();
        }
    }
}
