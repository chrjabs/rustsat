//! # Shared Facility Location Problem Encoding Tooling
//!
//! - Data types
//! - Input parser

use std::io;

/// An instance of the multi-objective assignment problem
#[derive(Clone, PartialEq, Eq, Default)]
pub struct FacilityLocation {
    n_objs: usize,
    n_customers: usize,
    n_facilities: usize,
    supply_cost: Vec<usize>,
    opening_cost: Vec<usize>,
}

impl FacilityLocation {
    pub fn from_file(reader: impl io::BufRead) -> anyhow::Result<Self> {
        parsing::parse_voptlib(reader)
    }

    pub fn n_objs(&self) -> usize {
        self.n_objs
    }

    pub fn n_customers(&self) -> usize {
        self.n_customers
    }

    pub fn n_facilities(&self) -> usize {
        self.n_facilities
    }

    fn cidx(&self, obj: usize, customer: usize, facility: usize) -> usize {
        debug_assert!(obj < self.n_objs);
        debug_assert!(customer < self.n_customers);
        debug_assert!(facility < self.n_facilities);
        obj * self.n_facilities * self.n_customers + customer * self.n_facilities + facility
    }

    fn ridx(&self, obj: usize, facility: usize) -> usize {
        debug_assert!(obj < self.n_objs);
        debug_assert!(facility < self.n_facilities);
        obj * self.n_facilities + facility
    }

    pub fn supply_cost(&self, obj: usize, customer: usize, facility: usize) -> usize {
        self.supply_cost[self.cidx(obj, customer, facility)]
    }

    pub fn opening_cost(&self, obj: usize, facility: usize) -> usize {
        self.opening_cost[self.ridx(obj, facility)]
    }
}

mod parsing {
    use std::io;

    use anyhow::Context;
    use nom::character::complete::u32;

    use crate::parsing::{callback_separated, single_value};

    macro_rules! next_line {
        ($reader:expr) => {{
            let mut buf = String::new();
            if $reader.read_line(&mut buf)? > 0 {
                Some(buf)
            } else {
                None
            }
        }};
    }

    pub fn parse_voptlib(mut reader: impl io::BufRead) -> anyhow::Result<super::FacilityLocation> {
        let line = next_line!(reader).context("file ended before number of users line")?;
        let (_, n_users) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of users line '{line}'"))?;
        let n_users = usize::try_from(n_users).context("u32 does not fit in usize")?;
        let line = next_line!(reader).context("file ended before number of services line")?;
        let (_, n_services) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of services line '{line}'"))?;
        let n_services = usize::try_from(n_services).context("u32 does not fit in usize")?;

        let mut prob = super::FacilityLocation {
            n_objs: 2,
            n_customers: n_users,
            n_facilities: n_services,
            ..super::FacilityLocation::default()
        };
        for _ in 0..2 {
            next_line!(reader).context("file ended early")?;
            for _ in 0..n_users {
                let line = next_line!(reader).context("file ended in the middle of c matrix")?;
                callback_separated(&line, u32, |value| {
                    let value = usize::try_from(value).context("u32 does not fit in usize")?;
                    prob.supply_cost.push(value);
                    Ok(())
                })
                .context("failed to parse c matrix line")?;
            }
        }

        for _ in 0..2 {
            next_line!(reader).context("file ended early")?;
            let line = next_line!(reader).context("file ended early")?;
            callback_separated(&line, u32, |value| {
                let value = usize::try_from(value).context("u32 does not fit in usize")?;
                prob.opening_cost.push(value);
                Ok(())
            })
            .context("failed to parse r vector")?;
        }

        Ok(prob)
    }

    #[cfg(test)]
    mod tests {
        use std::{fs::File, io::BufReader};

        #[test]
        fn voptlib() {
            let reader = BufReader::new(File::open("./data/didactic1.txt").unwrap());
            super::parse_voptlib(reader).unwrap();
        }
    }
}
