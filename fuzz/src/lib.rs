use rustsat::{
    encodings::{am1, card},
    instances::BasicVarManager,
    solvers::{Solve, SolveIncremental, SolverResult},
    types::{Lit, Var},
};
use rustsat_cadical::CaDiCaL;

const MAX_TEST_ASSIGNS: usize = 256;

/// A literal type the uses up to 16 bits
pub struct Lit16(Lit);

impl<'a> arbitrary::Arbitrary<'a> for Lit16 {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let data = u.arbitrary::<u16>()?;
        let neg = (data & 1u16) > 0;
        let idx = u32::from(data >> 1);
        Ok(Self(Lit::new(idx, neg)))
    }
}

impl From<Lit16> for Lit {
    fn from(val: Lit16) -> Self {
        val.0
    }
}

impl std::fmt::Debug for Lit16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

struct AssignIter {
    lits: Vec<(isize, Lit)>,
    offset: isize,
    mode: Mode,
}

enum Mode {
    Complete(Option<usize>),
    Random(fastrand::Rng, usize),
}

impl AssignIter {
    fn new(lits: &[Lit], max_assignments: usize, seed: u64) -> Self {
        let mut lits: Vec<_> = lits.iter().map(|&l| (1, l)).collect();
        let mut offset = 0;
        lits.sort_unstable();
        lits.dedup_by(|(_, a), (cnt, b)| {
            if a == b {
                *cnt += 1;
                return true;
            }
            if a.var() == b.var() {
                *cnt -= 1;
                offset += 1;
                return true;
            }
            false
        });
        if lits.len() < std::mem::size_of::<usize>() * 8
            && (1usize << lits.len()) <= max_assignments
        {
            Self {
                lits,
                offset,
                mode: Mode::Complete(Some(0)),
            }
        } else {
            Self {
                lits,
                offset,
                mode: Mode::Random(fastrand::Rng::with_seed(seed), max_assignments),
            }
        }
    }
}

impl Iterator for AssignIter {
    type Item = (usize, Vec<Lit>);

    fn next(&mut self) -> Option<Self::Item> {
        let (count, assign) = match &mut self.mode {
            Mode::Complete(ocurrent) => {
                let Some(current) = ocurrent else {
                    return None;
                };
                let mut assign = Vec::with_capacity(self.lits.len());
                let mut count = 0;
                for (idx, &(cnt, lit)) in self.lits.iter().enumerate() {
                    if (*current & (1usize << idx)) > 0 {
                        count += cnt;
                        assign.push(lit);
                    } else {
                        assign.push(!lit);
                    }
                }
                if let Some(next) = current.checked_add(1) {
                    if std::mem::size_of::<usize>() * 8
                        - usize::try_from(next.leading_zeros()).unwrap()
                        > self.lits.len()
                    {
                        *ocurrent = None;
                    } else {
                        *ocurrent = Some(next);
                    }
                } else {
                    *ocurrent = None;
                }
                (count, assign)
            }
            Mode::Random(rng, left) => {
                if *left == 0 {
                    return None;
                }
                *left -= 1;
                let mut assign = Vec::with_capacity(self.lits.len());
                let mut count = 0;
                for &(cnt, lit) in &self.lits {
                    if rng.bool() {
                        assign.push(lit);
                        count += cnt;
                    } else {
                        assign.push(!lit);
                    }
                }
                (count, assign)
            }
        };
        Some((usize::try_from(count + self.offset).unwrap(), assign))
    }
}

pub fn am1<AM1>(lits: &[Lit], seed: u64)
where
    AM1: am1::Encode + FromIterator<Lit>,
{
    #[cfg(feature = "dbg")]
    dbg!(lits);
    let max_var = lits.iter().copied().max().map_or(Var::new(0), |v| v.var());
    let mut var_manager = BasicVarManager::from_next_free(max_var + 1);
    let mut slv = CaDiCaL::default();
    let mut enc: AM1 = lits.iter().copied().collect();
    enc.encode(&mut slv, &mut var_manager).unwrap();

    for (count, assign) in AssignIter::new(lits, MAX_TEST_ASSIGNS, seed) {
        let res = slv.solve_assumps(&assign).unwrap();
        if count > 1 {
            assert_eq!(res, SolverResult::Unsat);
        } else {
            assert_eq!(res, SolverResult::Sat);
        }
    }
}

pub fn card<Card>(lits: &[Lit], bound: usize, seed: u64)
where
    Card: card::BoundUpper + FromIterator<Lit>,
{
    #[cfg(feature = "dbg")]
    dbg!(bound);
    #[cfg(feature = "dbg")]
    dbg!(lits);
    let max_var = lits.iter().copied().max().map_or(Var::new(0), |v| v.var());
    let mut var_manager = BasicVarManager::from_next_free(max_var + 1);
    let mut slv = CaDiCaL::default();
    let mut enc: Card = lits.iter().copied().collect();
    enc.encode_ub(bound..=bound, &mut slv, &mut var_manager)
        .unwrap();
    for unit in enc.enforce_ub(bound).unwrap() {
        slv.add_unit(unit).unwrap();
    }

    for (count, assign) in AssignIter::new(lits, MAX_TEST_ASSIGNS, seed) {
        let res = slv.solve_assumps(&assign).unwrap();
        if count > bound {
            assert_eq!(res, SolverResult::Unsat);
        } else {
            assert_eq!(res, SolverResult::Sat);
        }
    }
}
