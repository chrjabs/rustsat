//! # Shared Assignment Problem Encoding Tooling
//!
//! - Data types
//! - Input parser

use std::io;

/// An instance of the multi-objective assignment problem
#[derive(Clone, PartialEq, Eq)]
pub struct Assignment {
    pub(crate) n_tasks: usize,
    pub(crate) n_objs: usize,
    pub(crate) costs: Vec<usize>,
}

impl Assignment {
    fn empty(n_tasks: usize, n_objs: usize) -> Self {
        Self {
            n_tasks,
            n_objs,
            costs: vec![0; n_objs * n_tasks * n_tasks],
        }
    }

    pub fn from_file(reader: impl io::BufRead) -> anyhow::Result<Self> {
        parsing::parse_moolib(reader)
    }

    pub fn idx(&self, task: usize, agent: usize, obj: usize) -> usize {
        debug_assert!(task < self.n_tasks);
        debug_assert!(agent < self.n_tasks);
        debug_assert!(obj < self.n_objs);
        obj * self.n_tasks * self.n_tasks + task * self.n_tasks + agent
    }

    pub fn cost(&self, task: usize, agent: usize, obj: usize) -> usize {
        self.costs[self.idx(task, agent, obj)]
    }

    pub fn cost_mut(&mut self, task: usize, agent: usize, obj: usize) -> &mut usize {
        let idx = self.idx(task, agent, obj);
        self.costs.get_mut(idx).unwrap()
    }
}

mod parsing {
    use std::io;

    use anyhow::Context;
    use nom::character::complete::u32;

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

    pub fn parse_moolib(mut reader: impl io::BufRead) -> anyhow::Result<super::Assignment> {
        let line = next_non_comment_line!(reader)
            .context("file ended before number of objectives line")?;
        let (_, n_objs) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of objectives line '{line}'"))?;
        let line =
            next_non_comment_line!(reader).context("file ended before number of tasks line")?;
        let (_, n_tasks) = single_value(u32, "#")(&line)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse number of tasks line '{line}'"))?;
        let mut inst = super::Assignment::empty(n_tasks as usize, n_objs as usize);
        let mut buf = String::new();
        let mut depth = 0;
        let mut obj_idx = 0;
        let mut task_idx = 0;
        while reader.read_line(&mut buf)? > 0 {
            let mut remain = buf.trim_start();
            loop {
                if remain.starts_with('[') && depth < 2 {
                    depth += 1;
                    remain = &remain[1..];
                }
                if remain.starts_with(']') {
                    depth -= 1;
                    if depth == 1 {
                        task_idx = 0;
                    }
                    remain = &remain[1..];
                }
                if remain.starts_with(',') {
                    match depth {
                        1 => obj_idx += 1,
                        2 => task_idx += 1,
                        _ => unreachable!(),
                    };
                    remain = &remain[1..];
                }
                if remain.starts_with('#') || remain.trim().is_empty() {
                    break;
                }
                if depth == 2 {
                    let mut agent_idx = 0;
                    remain = callback_list(remain.trim_start(), u32, |value| {
                        anyhow::ensure!(obj_idx < n_objs, "too many objectives");
                        anyhow::ensure!(task_idx < n_tasks, "too many tasks");
                        anyhow::ensure!(agent_idx < n_tasks, "too many agents");
                        *inst.cost_mut(task_idx as usize, agent_idx as usize, obj_idx as usize) =
                            value as usize;
                        agent_idx += 1;
                        Ok(())
                    })?;
                }
            }
            buf.clear();
        }
        anyhow::ensure!(
            obj_idx + 1 == n_objs,
            "number of objectives does not match up"
        );
        Ok(inst)
    }

    #[cfg(test)]
    mod tests {
        use std::{fs::File, io::BufReader};

        #[test]
        fn moolib() {
            let reader = BufReader::new(File::open("./data/AP_p-3_n-5_ins-1.dat").unwrap());
            super::parse_moolib(reader).unwrap();
        }
    }
}
