//! # Small Executable For Profiling Tasks

use rustsat::{
    encodings::pb::{BoundUpper, DbGte},
    instances::{BasicVarManager, Cnf, ManageVars},
    lit,
    types::{Lit, Var},
};

macro_rules! lits {
    () => {
        // 50 random weights in 1..=50
        [
            (lit![0], 24),
            (lit![1], 30),
            (lit![2], 13),
            (lit![3], 11),
            (lit![4], 42),
            (lit![5], 6),
            (lit![6], 44),
            (lit![7], 14),
            (lit![8], 46),
            (lit![9], 9),
            (lit![10], 31),
            (lit![11], 31),
            (lit![12], 25),
            (lit![13], 24),
            (lit![14], 16),
            (lit![15], 50),
            (lit![16], 18),
            (lit![17], 23),
            (lit![18], 37),
            (lit![19], 11),
            (lit![20], 34),
            (lit![21], 1),
            (lit![22], 34),
            (lit![23], 46),
            (lit![24], 49),
            (lit![25], 6),
            (lit![26], 28),
            (lit![27], 46),
            (lit![28], 3),
            (lit![29], 9),
            (lit![30], 27),
            (lit![31], 35),
            (lit![32], 46),
            (lit![33], 9),
            (lit![34], 36),
            (lit![35], 4),
            (lit![36], 29),
            (lit![37], 46),
            (lit![38], 30),
            (lit![39], 28),
            (lit![40], 35),
            (lit![41], 30),
            (lit![42], 42),
            (lit![43], 4),
            (lit![44], 29),
            (lit![45], 5),
            (lit![46], 40),
            (lit![47], 46),
            (lit![48], 46),
            (lit![49], 35),
        ]
    };
}

fn build_full_ub<PBE: BoundUpper + FromIterator<(Lit, usize)>>(lits: &[(Lit, usize)]) {
    let mut enc = PBE::from_iter(lits.iter().copied());
    let max_var = lits
        .iter()
        .fold(Var::new(0), |mv, (lit, _)| std::cmp::max(lit.var(), mv));
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(max_var + 1);
    let mut collector = Cnf::new();
    enc.encode_ub(.., &mut collector, &mut var_manager).unwrap();
}

fn main() {
    for idx in 0..1 {
        build_full_ub::<DbGte>(&lits!());
        println!("iteration {}", idx);
    }
}
