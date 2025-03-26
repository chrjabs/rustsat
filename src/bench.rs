//! # Some Benchmarking Tests
//!
//! Running these requires nightly Rust, see [here](https://doc.rust-lang.org/unstable-book/library-features/test.html).

mod card_enc {
    extern crate test;

    use test::Bencher;

    use crate::{
        encodings::card::{BoundBoth, BoundLower, BoundUpper, DbTotalizer, Totalizer},
        instances::{BasicVarManager, Cnf, ManageVars},
        types::{Lit, Var},
    };

    fn build_full_ub<CE: BoundUpper + FromIterator<Lit>>(nlits: u32) {
        let mut enc = CE::from_iter((0..nlits).map(|idx| Lit::new(idx, false)));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(Var::new(nlits));
        let mut collector = Cnf::new();
        enc.encode_ub(.., &mut collector, &mut var_manager).unwrap();
    }

    fn build_full_lb<CE: BoundLower + FromIterator<Lit>>(nlits: u32) {
        let mut enc = CE::from_iter((0..nlits).map(|idx| Lit::new(idx, false)));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(Var::new(nlits));
        let mut collector = Cnf::new();
        enc.encode_lb(.., &mut collector, &mut var_manager).unwrap();
    }

    fn build_full_both<CE: BoundBoth + FromIterator<Lit>>(nlits: u32) {
        let mut enc = CE::from_iter((0..nlits).map(|idx| Lit::new(idx, false)));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(Var::new(nlits));
        let mut collector = Cnf::new();
        enc.encode_both(.., &mut collector, &mut var_manager)
            .unwrap();
    }

    #[bench]
    fn totalizer_ub(b: &mut Bencher) {
        b.iter(|| build_full_ub::<Totalizer>(1000));
    }

    #[bench]
    fn totalizer_lb(b: &mut Bencher) {
        b.iter(|| build_full_lb::<Totalizer>(1000));
    }

    #[bench]
    fn totalizer_both(b: &mut Bencher) {
        b.iter(|| build_full_both::<Totalizer>(1000));
    }

    #[bench]
    fn dbtotalizer_ub(b: &mut Bencher) {
        b.iter(|| build_full_ub::<DbTotalizer>(1000));
    }
}

mod pb_enc {
    extern crate test;

    use test::Bencher;

    use crate::{
        encodings::pb::{
            BinaryAdder, BoundUpper, DbGte, DynamicPolyWatchdog, GeneralizedTotalizer,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit,
        types::{Lit, Var},
    };

    macro_rules! lits {
        (small) => {
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
        (large) => {
            // 2 * 50 random weights in 1..=50
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
                (lit![50], 24),
                (lit![51], 30),
                (lit![52], 13),
                (lit![53], 11),
                (lit![54], 42),
                (lit![55], 6),
                (lit![56], 44),
                (lit![57], 14),
                (lit![58], 46),
                (lit![59], 9),
                (lit![60], 31),
                (lit![61], 31),
                (lit![62], 25),
                (lit![63], 24),
                (lit![64], 16),
                (lit![65], 50),
                (lit![66], 18),
                (lit![67], 23),
                (lit![68], 37),
                (lit![69], 11),
                (lit![70], 34),
                (lit![71], 1),
                (lit![72], 34),
                (lit![73], 46),
                (lit![74], 49),
                (lit![75], 6),
                (lit![76], 28),
                (lit![77], 46),
                (lit![78], 3),
                (lit![79], 9),
                (lit![80], 27),
                (lit![81], 35),
                (lit![82], 46),
                (lit![83], 9),
                (lit![84], 36),
                (lit![85], 4),
                (lit![86], 29),
                (lit![87], 46),
                (lit![88], 30),
                (lit![89], 28),
                (lit![90], 35),
                (lit![91], 30),
                (lit![92], 42),
                (lit![93], 4),
                (lit![94], 29),
                (lit![95], 5),
                (lit![96], 40),
                (lit![97], 46),
                (lit![98], 46),
                (lit![99], 35),
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

    #[bench]
    fn gte_ub(b: &mut Bencher) {
        b.iter(|| build_full_ub::<GeneralizedTotalizer>(&lits!(small)));
    }

    #[bench]
    fn dbgte_ub(b: &mut Bencher) {
        b.iter(|| build_full_ub::<DbGte>(&lits!(small)));
    }

    #[bench]
    fn dpw_ub(b: &mut Bencher) {
        b.iter(|| build_full_ub::<DynamicPolyWatchdog>(&lits!(small)));
    }

    #[bench]
    fn adder_ub(b: &mut Bencher) {
        b.iter(|| build_full_ub::<BinaryAdder>(&lits!(small)));
    }

    #[bench]
    fn gte_ub_large(b: &mut Bencher) {
        b.iter(|| build_full_ub::<GeneralizedTotalizer>(&lits!(large)));
    }

    #[bench]
    fn dbgte_ub_large(b: &mut Bencher) {
        b.iter(|| build_full_ub::<DbGte>(&lits!(large)));
    }

    #[bench]
    fn dpw_ub_large(b: &mut Bencher) {
        b.iter(|| build_full_ub::<DynamicPolyWatchdog>(&lits!(large)));
    }

    #[bench]
    fn adder_ub_large(b: &mut Bencher) {
        b.iter(|| build_full_ub::<BinaryAdder>(&lits!(large)));
    }
}

mod fio {
    extern crate test;

    use test::Bencher;

    use crate::instances::SatInstance;

    fn read_write_dimacs() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let inst: SatInstance =
            SatInstance::from_dimacs_path(format!("{manifest}/data/minisat-segfault.cnf")).unwrap();
        inst.write_dimacs_path("/tmp/rustsat-test.cnf").unwrap();
    }

    #[bench]
    fn read_write(b: &mut Bencher) {
        b.iter(|| read_write_dimacs());
    }
}
