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
    use rustsat::instances::fio::ParsingError;
    use winnow::{
        ascii::dec_uint,
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

    pub fn parse_moolib(mut reader: impl io::BufRead) -> anyhow::Result<super::Assignment> {
        let mut line_num = 0;
        let line = next_non_comment_line!(reader, line_num)
            .context("file ended before number of objectives line")?;
        let n_objs = single_value(dec_uint::<_, usize, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "number of objectives",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        let line = next_non_comment_line!(reader, line_num)
            .context("file ended before number of tasks line")?;
        let n_tasks = single_value(dec_uint::<_, usize, ContextError>, "#")
            .context(StrContext::Expected(StrContextValue::Description(
                "number of tasks",
            )))
            .parse(&line)
            .map_err(|e| ParsingError::from_parse(&e, &line, 0, line_num))?;
        let mut inst = super::Assignment::empty(n_tasks, n_objs);
        let mut buf = String::new();
        let mut depth = 0;
        let mut obj_idx = 0;
        let mut task_idx = 0;
        while reader.read_line(&mut buf)? > 0 {
            line_num += 1;
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
                        1 => {
                            obj_idx += 1;
                            anyhow::ensure!(obj_idx < n_objs, "too many objectives");
                        }
                        2 => {
                            task_idx += 1;
                            anyhow::ensure!(obj_idx < n_objs, "too many tasks");
                        }
                        _ => unreachable!(),
                    };
                    remain = &remain[1..];
                }
                if remain.starts_with('#') || remain.trim().is_empty() {
                    break;
                }
                if depth == 2 {
                    let mut agent_idx = 0;
                    remain = (
                        ListCallbackParser::new(
                            |value| {
                                if agent_idx >= n_tasks {
                                    let mut err = ContextError::new();
                                    err.push(StrContext::Expected(StrContextValue::Description(
                                        "too many agents",
                                    )));
                                    return Err(err);
                                }
                                *inst.cost_mut(task_idx, agent_idx, obj_idx) = value;
                                agent_idx += 1;
                                Ok(())
                            },
                            dec_uint::<_, usize, ContextError>,
                        )
                        .context(StrContext::Expected(
                            StrContextValue::Description("list of values"),
                        )),
                        rest,
                    )
                        .parse(remain)
                        .map_err(|e| {
                            ParsingError::from_parse(
                                &e,
                                &buf,
                                rustsat::utils::substr_offset(&buf, remain).unwrap(),
                                line_num,
                            )
                        })?
                        .1;
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
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let reader = BufReader::new(
                File::open(format!("{manifest}/data/AP_p-3_n-5_ins-1.dat")).unwrap(),
            );
            super::parse_moolib(reader).unwrap();
        }
    }
}
