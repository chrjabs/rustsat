#![cfg(cadical_feature = "ipasir-up")]

mod decisions {
    use rustsat::{
        instances::{BasicVarManager, SatInstance},
        solvers::{Solve, SolveStats, SolverResult},
        types::{Lit, Var},
    };

    struct ForceDecisions {
        trail: Vec<Lit>,
        levels: Vec<usize>,
        next_unassigned: Var,
        assigned: Vec<bool>,
        n_decisions: usize,
    }

    impl ForceDecisions {
        fn init(solver: &mut rustsat_cadical::CaDiCaL) -> rustsat_cadical::PropagatorHandle<Self> {
            let n_vars = solver.n_vars();
            let prop = ForceDecisions {
                trail: Vec::with_capacity(n_vars),
                levels: vec![],
                next_unassigned: Var::new(0),
                assigned: vec![false; n_vars],
                n_decisions: 0,
            };
            let handle = solver.connect_propagator(prop);
            for idx in 0..(n_vars as u32) {
                solver.add_observed_var(Var::new(idx));
            }
            handle
        }

        fn find_next_unassigned(&self) -> Var {
            let mut unassigned = self.next_unassigned;
            while self.assigned[unassigned.idx()] {
                unassigned += 1;
            }
            unassigned
        }
    }

    impl rustsat_cadical::ExternalPropagate for ForceDecisions {
        fn assignment(&mut self, lits: rustsat_cadical::AssignmentIter) {
            for lit in lits {
                self.assigned[lit.vidx()] = true;
                self.trail.push(lit);
            }
        }

        fn new_decision_level(&mut self) {
            self.levels.push(self.trail.len());
        }

        fn backtrack(&mut self, new_level: usize) {
            let drain_from = self.levels[new_level];
            self.levels.drain(new_level + 1..);
            for lit in self.trail.drain(drain_from..) {
                self.assigned[lit.vidx()] = false;
            }
            self.next_unassigned = Var::new(0);
        }

        fn decide(&mut self) -> Option<Lit> {
            let this = self.find_next_unassigned();
            self.next_unassigned = this + 1;
            self.n_decisions += 1;
            Some(this.pos_lit())
        }
    }

    #[test]
    fn forced_decisions() {
        let mut solver = rustsat_cadical::CaDiCaL::default();

        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let inst = SatInstance::<BasicVarManager>::from_dimacs_path(format!(
            "{manifest}/data/prime121.cnf"
        ))
        .expect("failed to parse instance");
        solver
            .add_cnf_ref(inst.cnf())
            .expect("failed to add cnf to solver");

        let handle = ForceDecisions::init(&mut solver);

        let res = solver.solve().expect("failed solving");
        assert_eq!(res, SolverResult::Sat);

        let prop = solver.disconnect_propagator(handle);
        dbg!(prop.n_decisions);
        assert!(prop.n_decisions > 0);
    }
}

mod hcp_cegar {
    // Based on https://github.com/kfazekas/incremental-examples/blob/main/4_ipasirup/hcp_ipasirup.cpp

    use std::io::BufRead;

    use rustsat::{
        encodings::am1::{Encode, Pairwise},
        instances::BasicVarManager,
        solvers::{Solve, SolveStats, SolverResult},
        types::{Lit, Var},
    };
    use rustsat_cadical::ExternalClause;

    struct UnionFind {
        rank: Vec<usize>,
        parent: Vec<usize>,
        n: usize,
    }

    impl UnionFind {
        fn new(n: usize) -> Self {
            let mut parent = Vec::with_capacity(n);
            for i in 0..n {
                parent.push(i);
            }
            assert_eq!(parent.len(), n);
            Self {
                rank: vec![0; n],
                parent,
                n,
            }
        }

        fn find(&mut self, x: usize) -> usize {
            if self.parent[x] != x {
                self.parent[x] = self.find(self.parent[x]);
            }
            self.parent[x]
        }

        fn union(&mut self, x: usize, y: usize) {
            let xset = self.find(x);
            let yset = self.find(y);

            if xset == yset {
                return;
            }

            if self.rank[xset] < self.rank[yset] {
                self.parent[xset] = yset;
            } else if self.rank[xset] > self.rank[yset] {
                self.parent[yset] = xset;
            } else {
                self.parent[yset] = xset;
                self.rank[xset] = self.rank[xset] + 1;
            }
        }
    }

    struct CycleBreaker {
        trail: Vec<Lit>,
        levels: Vec<usize>,
        blocking_clause: Option<ExternalClause>,
        lookup_src: Vec<usize>,
        lookup_dst: Vec<usize>,
        chains: UnionFind,
    }

    impl CycleBreaker {
        fn init(
            adj_mtx: &[Vec<Option<Var>>],
            solver: &mut rustsat_cadical::CaDiCaL,
        ) -> rustsat_cadical::PropagatorHandle<Self> {
            let n_vars = solver.n_vars();
            let mut breaker = CycleBreaker {
                trail: Vec::with_capacity(n_vars),
                levels: vec![],
                blocking_clause: None,
                lookup_src: vec![0; n_vars],
                lookup_dst: vec![0; n_vars],
                chains: UnionFind::new(adj_mtx.len()),
            };
            for (i, col) in adj_mtx.iter().enumerate() {
                for (j, var) in col.iter().enumerate() {
                    if let Some(var) = var {
                        breaker.lookup_src[var.idx()] = i;
                        breaker.lookup_dst[var.idx()] = j;
                    }
                }
            }
            let handle = solver.connect_propagator(breaker);
            for idx in 0..(n_vars as u32) {
                solver.add_observed_var(Var::new(idx));
            }
            handle
        }
    }

    impl rustsat_cadical::ExternalPropagate for CycleBreaker {
        fn assignment(&mut self, lits: rustsat_cadical::AssignmentIter) {
            todo!()
        }

        fn new_decision_level(&mut self) {
            self.levels.push(self.trail.len());
        }

        fn backtrack(&mut self, new_level: usize) {
            let drain_from = self.levels[new_level];
            self.levels.drain(new_level + 1..);
            todo!()
        }

        fn external_clause(&mut self) -> Option<rustsat_cadical::ExternalClause> {
            self.blocking_clause.take()
        }
    }

    fn init_solver<P>(path: P) -> rustsat_cadical::CaDiCaL<'static, 'static>
    where
        P: AsRef<std::path::Path>,
    {
        let mut adj_mtx = vec![];
        let mut next_var = Var::new(0);
        let mut n_nodes = 0;

        // Parse adjencency matrix
        for line in
            std::io::BufReader::new(std::fs::File::open(path).expect("failed to open file")).lines()
        {
            let line = line.expect("failed to read line");
            if line.starts_with("DIMENSION :") {
                n_nodes = line.trim_end().rsplit_once(' ').unwrap().1.parse().unwrap();
                adj_mtx = vec![vec![None; n_nodes]; n_nodes];
            } else if line.trim().is_empty() || !line.chars().next().unwrap().is_digit(10) {
                continue;
            }
            assert!(!adj_mtx.is_empty());
            let (node_a, node_b) = line.trim_end().split_once(' ').unwrap();
            let node_a: usize = node_a.parse().unwrap();
            let node_b: usize = node_b.parse().unwrap();
            assert!(adj_mtx[node_a - 1][node_b - 1].is_none());
            adj_mtx[node_a - 1][node_b - 1] = Some(next_var);
            next_var += 1;
            adj_mtx[node_b - 1][node_a - 1] = Some(next_var);
            next_var += 1;
        }

        let mut solver = rustsat_cadical::CaDiCaL::default();
        solver.set_option("chrono", 0).unwrap();
        solver.set_option("inprocessing", 0).unwrap();

        // Add degree constraints
        // Note that this doesn't add any new variables, so this var manager is a dummy
        let mut vm = BasicVarManager::default();
        // Exactly one outgoing edge is selected
        for col in adj_mtx.iter() {
            let neighbours: Vec<_> = col.iter().flatten().map(|v| v.pos_lit()).collect();
            // <= 1
            let mut am1: Pairwise = neighbours.iter().copied().collect();
            am1.encode(&mut solver, &mut vm).unwrap();
            // >= 1
            solver.add_clause(neighbours.into()).unwrap();
        }
        // Exactly one incoming edge is selected
        for col in adj_mtx.iter() {
            let neighbours: Vec<_> = col.iter().flatten().map(|v| v.pos_lit()).collect();
            // <= 1
            let mut am1: Pairwise = neighbours.iter().copied().collect();
            am1.encode(&mut solver, &mut vm).unwrap();
            // >= 1
            solver.add_clause(neighbours.into()).unwrap();
        }

        // No 2-long subcycles
        for (i, col) in adj_mtx.iter().enumerate() {
            for (j, var_a) in col.iter().enumerate().skip(i + 1) {
                if let Some(var_a) = var_a {
                    solver
                        .add_binary(var_a.neg_lit(), adj_mtx[j][i].unwrap().neg_lit())
                        .unwrap();
                }
            }
        }

        todo!("connect cycle breaker");

        solver
    }

    #[test]
    fn graph2() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let mut solver = init_solver(format!("{manifest}/data/fhcpcs-graph2.hpc"));
        let res = solver.solve().unwrap();
        assert_eq!(res, SolverResult::Sat);
        todo!("check solution")
    }
}
