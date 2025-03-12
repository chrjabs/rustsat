/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "subsumestrengthen.h"
#include "occsimplifier.h"
#include "solver.h"
#include "watchalgos.h"
#include "clauseallocator.h"
#include "sqlstats.h"
#include "solver.h"
#include "solvertypes.h"
#include "subsumeimplicit.h"
#include <algorithm>
#include <array>

//#define VERBOSE_DEBUG

using namespace CMSat;

SubsumeStrengthen::SubsumeStrengthen(
    OccSimplifier* _simplifier
    , Solver* _solver
) :
    simplifier(_simplifier)
    , solver(_solver)
{
}

Sub0Ret SubsumeStrengthen::backw_sub_with_long(const ClOffset offset)
{
    Clause& cl = *solver->cl_alloc.ptr(offset);
    assert(!cl.getRemoved());
    assert(!cl.freed());

    #ifdef VERBOSE_DEBUG
    cout << "subsume-ing with clause: " << cl << endl;
    #endif

    Sub0Ret ret = subsume_and_unlink(
        offset
        , cl
        , cl.abst
    );

    //If irred is subsumed by redundant, make the redundant into irred
    if (cl.red() && ret.subsumedIrred) {
        STATS_DO(solver->stats_del_cl(&cl));
        cl.makeIrred();
        solver->litStats.redLits -= cl.size();
        solver->litStats.irredLits += cl.size();
        if (!cl.getOccurLinked()) {
            simplifier->link_in_clause(cl);
        } else {
            for(const Lit l: cl) {
                simplifier->n_occurs[l.toInt()]++;
                simplifier->elim_calc_need_update.touch(l);
                simplifier->added_cl_to_var.touch(l);
            }
        }
    }

    //Update stats
    cl.stats = ClauseStats::combineStats(cl.stats, ret.stats);
    #if defined(STATS_NEEDED) || defined (FINAL_PREDICTOR)
    if (cl.red()) {
        auto& extra_stats = solver->red_stats_extra[cl.stats.extra_pos];
        extra_stats = ClauseStatsExtra::combineStats(extra_stats, ret.stats_extra);
    }
    #endif

    return ret;
}
template Sub0Ret SubsumeStrengthen::subsume_and_unlink(
    const ClOffset offset
    , const vector<Lit>& ps
    , const cl_abst_type abs
);

/**
@brief Backward-subsumption using given clause
*/
template<class T>
Sub0Ret SubsumeStrengthen::subsume_and_unlink(
    const ClOffset offset
    , const T& ps
    , const cl_abst_type abs
) {
    Sub0Ret ret;

    subs.clear();
    find_subsumed(offset, ps, abs, subs);

    //Go through each clause that can be subsumed
    for (const auto& occ_cl: subs) {
        if (!occ_cl.ws.isClause()) {
            continue;
        }
        ClOffset off = occ_cl.ws.get_offset();
        Clause *tmpcl = solver->cl_alloc.ptr(off);

        //-> ID kept will be 1st parameter
        //Stats will be merged together here then merged into the
        //subsuming clause's stats
        ret.stats = ClauseStats::combineStats(tmpcl->stats, ret.stats);
        #if defined(STATS_NEEDED) || defined(FINAL_PREDICTOR)
        if (tmpcl->red()) {
            ret.stats_extra = ClauseStatsExtra::combineStats(
                solver->red_stats_extra[tmpcl->stats.extra_pos],
                ret.stats_extra);
        }
        #endif
        VERBOSE_PRINT("-> subsume removing:" << *tmpcl);

        ret.subsumedIrred |= !tmpcl->red();
        simplifier->unlink_clause(off, true, false, true);
        ret.numSubsumed++;

        //If we are waaay over time, just exit
        if (*simplifier->limit_to_decrease < -20LL*1000LL*1000LL)
            break;
    }

    return ret;
}

bool SubsumeStrengthen::backw_sub_str_with_long(
    const ClOffset offset,
    Sub1Ret& ret_sub_str)
{
    subs.clear();
    subsLits.clear();
    Clause& cl = *solver->cl_alloc.ptr(offset);
    assert(!cl.getRemoved());
    assert(!cl.freed());

    if (solver->conf.verbosity >= 6)
        cout << "backw_sub_str_with_long-ing with clause:" << cl
            << " offset: " << offset << endl;

    find_subsumed_and_strengthened(
        offset
        , cl
        , cl.abst
        , subs
        , subsLits
    );

    for (size_t j = 0
        ; j < subs.size() && solver->okay() && *simplifier->limit_to_decrease > -20LL*1000LL*1000LL
        ; j++
    ) {
        assert(subs[j].ws.isClause());
        ClOffset offset2 = subs[j].ws.get_offset();
        Clause& cl2 = *solver->cl_alloc.ptr(offset2);
        if (cl2.used_in_xor() &&
            solver->conf.force_preserve_xors)
        {
            continue;
        }

        if (subsLits[j] == lit_Undef) {  //Subsume
            VERBOSE_PRINT("subsumed clause " << cl2);

            //If subsumes a irred, and is redundant, make it irred
            if (cl.red()
                && !cl2.red()
            ) {
                STATS_DO(solver->stats_del_cl(&cl));
                cl.makeIrred();
                solver->litStats.redLits -= cl.size();
                solver->litStats.irredLits += cl.size();
                if (!cl.getOccurLinked()) {
                    simplifier->link_in_clause(cl);
                } else {
                    for(const Lit l: cl) {
                        simplifier->n_occurs[l.toInt()]++;
                    }
                }
            }

            //Update stats
            cl.stats = ClauseStats::combineStats(cl.stats, cl2.stats);
            #if defined(STATS_NEEDED) || defined (FINAL_PREDICTOR)
            if (cl.red() && cl2.red()) {
                auto& extra_stats = solver->red_stats_extra[cl.stats.extra_pos];
                auto& extra_stats2 = solver->red_stats_extra[cl2.stats.extra_pos];
                extra_stats = ClauseStatsExtra::combineStats(extra_stats, extra_stats2);
            }
            #endif

            //this will handle touching all vars for elim re-calc
            simplifier->unlink_clause(offset2, true, false, true);
            ret_sub_str.sub++;
        } else { //Strengthen
            VERBOSE_PRINT("strenghtened clause " << cl2);
            if (cl2.used_in_xor() &&
                solver->conf.force_preserve_xors)
            {
                continue;
            }
            if (!simplifier->remove_literal(offset2, subsLits[j], true)) {
                return false;
            }
            ret_sub_str.str++;
        }
    }

    return solver->okay();
}

void SubsumeStrengthen::backw_sub_long_with_long()
{
    //If clauses are empty, the system below segfaults
    if (simplifier->clauses.empty())
        return;

    double myTime = cpuTime();
    size_t wenThrough = 0;
    Sub0Ret sub0ret;
    const int64_t orig_limit = simplifier->subsumption_time_limit;
    std::shuffle(simplifier->clauses.begin(), simplifier->clauses.end(), solver->mtrand);
    const size_t max_go_through =
        solver->conf.subsume_gothrough_multip*(double)simplifier->clauses.size();

    while (*simplifier->limit_to_decrease > 0
        && wenThrough < max_go_through
    ) {
        *simplifier->limit_to_decrease -= 3;
        wenThrough++;

        //Print status
        if (solver->conf.verbosity >= 5
            && wenThrough % 10000 == 0
        ) {
            cout << "toDecrease: " << *simplifier->limit_to_decrease << endl;
        }

        const size_t at = wenThrough % simplifier->clauses.size();
        const ClOffset offset = simplifier->clauses[at];
        Clause* cl = solver->cl_alloc.ptr(offset);

        //Has already been removed
        if (cl->freed() || cl->getRemoved())
            continue;


        *simplifier->limit_to_decrease -= 10;
        sub0ret += backw_sub_with_long(offset);
    }

    const double time_used = cpuTime() - myTime;
    const bool time_out = (*simplifier->limit_to_decrease <= 0);
    const double time_remain = float_div(*simplifier->limit_to_decrease, orig_limit);
    if (solver->conf.verbosity) {
        cout
        << "c [occ-backw-sub-long-w-long] rem cl: " << sub0ret.numSubsumed
        << " tried: " << wenThrough << "/" << simplifier->clauses.size()
        << " (" << std::setprecision(1) << std::fixed
        << stats_line_percent(wenThrough, simplifier->clauses.size())
        << "%)"
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "occ-backw-sub-long-w-long"
            , time_used
            , time_out
            , time_remain
        );
    }

    //Update time used
    runStats.sub0 += sub0ret;
    runStats.subsumeTime += cpuTime() - myTime;
}

bool SubsumeStrengthen::backw_str_long_with_long()
{
    assert(solver->ok);

    double myTime = cpuTime();
    size_t wenThrough = 0;
    const int64_t orig_limit = *simplifier->limit_to_decrease;
    Sub1Ret ret;

    std::shuffle(simplifier->clauses.begin(), simplifier->clauses.end(), solver->mtrand);
    while(*simplifier->limit_to_decrease > 0
        && wenThrough < 1.5*(double)2*simplifier->clauses.size()
        && solver->okay()
    ) {
        *simplifier->limit_to_decrease -= 10;
        wenThrough++;

        //Print status
        if (solver->conf.verbosity >= 5
            && wenThrough % 10000 == 0
        ) {
            cout << "toDecrease: " << *simplifier->limit_to_decrease << endl;
        }

        const size_t at = wenThrough % simplifier->clauses.size();
        ClOffset offset = simplifier->clauses[at];
        Clause* cl = solver->cl_alloc.ptr(offset);

        //Has already been removed
        if (cl->freed() || cl->getRemoved())
            continue;

        if (!backw_sub_str_with_long(offset, ret)) {
            return false;
        }

    }

    const double time_used = cpuTime() - myTime;
    const bool time_out = *simplifier->limit_to_decrease <= 0;
    const double time_remain = float_div(*simplifier->limit_to_decrease, orig_limit);

    if (solver->conf.verbosity) {
        cout
        << "c [occ-backw-sub-str-long-w-long]"
        << " sub: " << ret.sub
        << " str: " << ret.str
        << " tried: " << wenThrough << "/" << simplifier->clauses.size()
        << " ("
        << stats_line_percent(wenThrough, simplifier->clauses.size())
        << ") "
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "occ-backw-sub-str-long-w-long"
            , time_used
            , time_out
            , time_remain
        );
    }

    //Update time used
    runStats.sub1 += ret;
    runStats.strengthenTime += cpuTime() - myTime;

    return solver->okay();
}

/**
@brief Helper function for find_subsumed_and_strengthened

Used to avoid duplication of code
*/
template<class T>
void inline SubsumeStrengthen::fill_sub_str(
    const ClOffset offset
    , const T& cl
    , const cl_abst_type abs
    , vector<OccurClause>& out_subsumed
    , vector<Lit>& out_lits
    , const Lit lit // this variable is in the "cl", but may be inverted
    , bool inverted // whether "lit" is inverted
) {
    Lit litSub;
    uint32_t num_bin_found = 0;
    watch_subarray_const cs = solver->watches[lit];

    //Do subsume only for the moment
    //TODO strengthening
    Lit bin_other_lit = lit_Undef;
    if (cl.size() == 2) {
        if (lit == (cl[0]^inverted)) {
            bin_other_lit = cl[1];
        } else if (lit == (cl[1]^inverted)) {
            bin_other_lit = cl[0];
        }
    }

    *simplifier->limit_to_decrease -= (long)cs.size()*2+ 40;
    for (const auto& w: cs) {
        if (w.isBin()) {
            if (cl.size() > 2) {
                continue;
            }

            if (w.red()) {
                //let's ignore
                continue;
            }

            if (w.lit2() != bin_other_lit) {
                continue;
            }

            if (inverted) {
                out_subsumed.push_back(OccurClause(lit, w));
                out_lits.push_back(bin_other_lit);
            } else {
                //Don't delete ourselves
                num_bin_found++;
                if (num_bin_found <= 1) {
                    continue;
                }
                out_subsumed.push_back(OccurClause(lit, w));
                out_lits.push_back(lit_Undef);
            }
            continue;
        }

        assert(w.isClause());
        if (w.get_offset() == offset
            || !subsetAbst(abs, w.getAbst())
        ) {
            continue;
        }

        ClOffset offset2 = w.get_offset();
        const Clause& cl2 = *solver->cl_alloc.ptr(offset2);
        if (cl2.getRemoved()
            || cl.size() > cl2.size())
        {
            continue;
        }

        *simplifier->limit_to_decrease -= (long)((cl.size() + cl2.size())/4);
        litSub = subset1(cl, cl2);
        if (litSub != lit_Error) {
            out_subsumed.push_back(OccurClause(lit, w));
            out_lits.push_back(litSub);

            #ifdef VERBOSE_DEBUG
            if (litSub == lit_Undef) cout << "subsume-d: ";
            else cout << "backw_sub_str_with_long-ed (lit: "
                << litSub
                << ") clause offset: "
                << w.get_offset()
                << endl;
            #endif
        }
    }
}

/**
@brief Checks if clauses are subsumed or could be strenghtened with given clause

Checks if:
* any clause is subsumed with given clause
* the given clause could perform self-subsuming resolution on any other clause

@param[in] ps The clause to perform the above listed algos with
@param[in] abs The abstraction of clause ps
@param[out] out_subsumed The clauses that could be modified by ps
@param[out] out_lits Defines HOW these clauses could be modified. By removing
literal, or by subsumption (in this case, there is lit_Undef here)
*/
template<class T>
void SubsumeStrengthen::find_subsumed_and_strengthened(
    ClOffset offset
    , const T& cl
    , const cl_abst_type abs
    , vector<OccurClause>& out_subsumed
    , vector<Lit>& out_lits
)
{
    #ifdef VERBOSE_DEBUG
    cout << "find_subsumed_and_strengthened: " << cl << endl;
    #endif

    Lit minLit = lit_Undef;
    uint32_t bestSize = numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < cl.size(); i++){
        uint32_t newSize =
            solver->watches[cl[i]].size()
                + solver->watches[~cl[i]].size();

        if (newSize < bestSize) {
            minLit = cl[i];
            bestSize = newSize;
        }
    }
    assert(minLit != lit_Undef);
    *simplifier->limit_to_decrease -= (long)cl.size();

    fill_sub_str(offset, cl, abs, out_subsumed, out_lits, minLit, false);
    fill_sub_str(offset, cl, abs, out_subsumed, out_lits, ~minLit, true);
}

//must be called from deal_with_added_long_and_bin
bool SubsumeStrengthen::handle_added_long_cl(const bool verbose)
{
    assert(solver->prop_at_head());

    int64_t orig_limit = *simplifier->limit_to_decrease;
    size_t origTrailSize = solver->trail_size();
    const double start_time = cpuTime();
    Sub1Ret stat;

    //NOTE added_long_cl CAN CHANGE while the below is running!
    uint32_t i = 0;
    for(; i < simplifier->added_long_cl.size()
        && *simplifier->limit_to_decrease >= 0
        ; i++
    ) {
        const ClOffset offs = simplifier->added_long_cl[i];
        Clause* cl = solver->cl_alloc.ptr(offs);
        if (cl->freed() || cl->getRemoved()) continue;
        cl->stats.marked_clause = 0;
        if (!backw_sub_str_with_long(offs, stat)) goto end;
        if ((i&0xfff) == 0xfff && solver->must_interrupt_asap()) goto end;
    }

    end:
    //we still have to clear the marks
    for(; i < simplifier->added_long_cl.size(); i ++) {
        ClOffset off = simplifier->added_long_cl[i];
        Clause* cl = solver->cl_alloc.ptr(off);
        if (cl->freed() || cl->getRemoved()) continue;
        cl->stats.marked_clause = 0;
    }
    simplifier->added_long_cl.clear();

    if (verbose) {
        const bool time_out =  *simplifier->limit_to_decrease <= 0;
        const double time_used = cpuTime() - start_time;
        const double time_remain = float_div(*simplifier->limit_to_decrease, orig_limit);
        if (solver->conf.verbosity) {
            cout
            << "c [occ-backw-sub-str-w-added-long] "
            << " sub: " << stat.sub
            << " str: " << stat.str
            << " 0-depth ass: " << solver->trail_size() - origTrailSize
            << solver->conf.print_times(time_used, time_out, time_remain)
            << endl;
        }
        if (solver->sqlStats) {
            solver->sqlStats->time_passed(
                solver
                , "occ-backw-sub-str-w-added-long"
                , time_used
                , time_out
                , time_remain
            );
        }
    }

    return solver->okay();
}

//A subsumes B (A <= B)
template<class T1, class T2>
bool SubsumeStrengthen::subset(const T1& A, const T2& B)
{
    #ifdef MORE_DEUBUG
    cout << "A:" << A << endl;
    for(size_t i = 1; i < A.size(); i++) {
        assert(A[i-1] < A[i]);
    }

    cout << "B:" << B << endl;
    for(size_t i = 1; i < B.size(); i++) {
        assert(B[i-1] < B[i]);
    }
    #endif

    bool ret;
    uint32_t i = 0;
    uint32_t i2;
    Lit lastB = lit_Undef;
    for (i2 = 0; i2 < B.size(); i2++) {
        if (lastB != lit_Undef)
            assert(lastB < B[i2]);

        lastB = B[i2];
        //Literals are ordered
        if (A[i] < B[i2]) {
            ret = false;
            goto end;
        }
        else if (A[i] == B[i2]) {
            i++;

            //went through the whole of A now, so A subsumes B
            if (i == A.size()) {
                ret = true;
                goto end;
            }
        }
    }
    ret = false;

    end:
    *simplifier->limit_to_decrease -= (long)i2*4 + (long)i*4;
    return ret;
}

/**
@brief Decides if A subsumes B, or if not, if A could strenghten B

@note: Assumes 'seen' is cleared (will leave it cleared)

Helper function for strengthening. Does two things in one go:
1) decides if clause A could subsume clause B
2) decides if clause A could be used to perform self-subsuming resoltuion on
clause B

@return lit_Error, if neither (1) or (2) is true. Returns lit_Undef (1) is true,
and returns the literal to remove if (2) is true
*/
template<class T1, class T2>
Lit SubsumeStrengthen::subset1(const T1& A, const T2& B)
{
    Lit retLit = lit_Undef;

    uint32_t i = 0;
    uint32_t i2;
    for (i2 = 0; i2 < B.size(); i2++) {
        if (A[i] == ~B[i2] && retLit == lit_Undef) {
            retLit = B[i2];
            i++;
            if (i == A.size())
                goto end;

            continue;
        }

        //Literals are ordered
        if (A[i] < B[i2]) {
            retLit = lit_Error;
            goto end;
        }

        if (A[i] == B[i2]) {
            i++;

            if (i == A.size())
                goto end;
        }
    }
    retLit = lit_Error;

    end:
    *simplifier->limit_to_decrease -= (long)i2*4 + (long)i*4;
    return retLit;
}

template<class T>
uint32_t SubsumeStrengthen::find_smallest_watchlist_for_clause(const T& ps) const
{
    uint32_t min_i = 0;
    size_t min_num = solver->watches[ps[min_i]].size();
    for (uint32_t i = 1; i < ps.size(); i++){
        const size_t this_num = solver->watches[ps[i]].size();
        if (this_num < min_num) {
            min_i = i;
            min_num = this_num;
        }
    }
    *simplifier->limit_to_decrease -= (long)ps.size();

    return min_i;
}

/**
@brief Finds clauses that are backward-subsumed by given clause

Only handles backward-subsumption. Uses occurrence lists
@param[out] out_subsumed The set of clauses subsumed by the given
*/
template<class T> void SubsumeStrengthen::find_subsumed(
    const ClOffset offset //Will not match with index of the name value
    , const T& ps //Literals in clause
    , const cl_abst_type abs //Abstraction of literals in clause
    , vector<OccurClause>& out_subsumed //List of clauses
    , bool only_irred
) {
    #ifdef VERBOSE_DEBUG
    cout << "find_subsumed: ";
    for (const Lit lit: ps) {
        cout << lit << " , ";
    }
    cout << endl;
    #endif

    const uint32_t smallest = find_smallest_watchlist_for_clause(ps);
    const Lit lit = ps[smallest];

    //Go through the occur list of the literal that has the smallest occur list
    watch_subarray occ = solver->watches[lit];
    *simplifier->limit_to_decrease -= (long)occ.size()*8 + 40;

    //cout << "find_subsumed going through: " << solver->watches_to_string(lit, occ) << endl;
    for (const auto& w: occ) {
        if (w.isBin()
            && ps.size() == 2
            && ps[!smallest] == w.lit2()
            && !w.red()
        ) {
            out_subsumed.push_back(OccurClause(lit, w));
        }

        if (!w.isClause()) {
            continue;
        }

        *simplifier->limit_to_decrease -= 15;

        if (w.get_offset() == offset
            || !subsetAbst(abs, w.getAbst())
        ) {
            continue;
        }

        const ClOffset offset2 = w.get_offset();
        Clause& cl2 = *solver->cl_alloc.ptr(offset2);

        if (ps.size() > cl2.size() ||
            cl2.getRemoved() ||
            (only_irred && cl2.red()))
        {
            continue;
        }

        *simplifier->limit_to_decrease -= 50;
        if (subset(ps, cl2)) {
            out_subsumed.push_back(OccurClause(lit, w));
            #ifdef VERBOSE_DEBUG
            cout << "subsumed cl offset: " << offset2 << endl;
            #endif
        }
    }
}
template void SubsumeStrengthen::find_subsumed(
    const ClOffset offset
    , const std::array<Lit, 2>& ps
    , const cl_abst_type abs //Abstraction of literals in clause
    , vector<OccurClause>& out_subsumed //List of clause indexes subsumed
    , bool only_irred
);
template void SubsumeStrengthen::find_subsumed(
    const ClOffset offset
    , const vector<Lit>& ps
    , const cl_abst_type abs //Abstraction of literals in clause
    , vector<OccurClause>& out_subsumed //List of clause indexes subsumed
    , bool only_irred
);

size_t SubsumeStrengthen::mem_used() const
{
    size_t b = 0;
    b += subs.capacity()*sizeof(ClOffset);
    b += subsLits.capacity()*sizeof(Lit);

    return b;
}

void SubsumeStrengthen::remove_binary_cl(const OccurClause& cl)
{
    solver->detach_bin_clause(
        cl.lit, cl.ws.lit2(), cl.ws.red(), cl.ws.get_ID());
    (*solver->frat) << del << cl.ws.get_ID() << cl.lit << cl.ws.lit2() << fin;
    if (!cl.ws.red()) {
        simplifier->n_occurs[cl.lit.toInt()]--;
        simplifier->n_occurs[cl.ws.lit2().toInt()]--;
        simplifier->elim_calc_need_update.touch(cl.lit);
        simplifier->elim_calc_need_update.touch(cl.ws.lit2());
        simplifier->removed_cl_with_var.touch(cl.lit);
        simplifier->removed_cl_with_var.touch(cl.ws.lit2());
    }
}

//Implicit input here is ALWAY irred
bool SubsumeStrengthen::backw_sub_str_with_impl(
    const vector<Lit>& lits,
    Sub1Ret& ret_sub_str
) {
    subs.clear();
    subsLits.clear();

    find_subsumed_and_strengthened(
        CL_OFFSET_MAX
        , lits
        , calcAbstraction(lits)
        , subs
        , subsLits
    );

    for (size_t j = 0
        ; j < subs.size() && solver->okay()
        ; j++
    ) {
        if (subs[j].ws.isBin()) {
            if (subsLits[j] == lit_Undef) { //subsume
                remove_binary_cl(subs[j]);
            } else { //strengthen
                lbool val = solver->value(subsLits[j]);
                const int32_t ID = ++solver->clauseID;
                if (val == l_False) {
                    (*solver->frat) << add << ID << subsLits[j] << fin;
                    (*solver->frat) << add << ++solver->clauseID << fin;
                    assert(solver->unsat_cl_ID == 0);
                    solver->unsat_cl_ID = solver->clauseID;
                    solver->ok = false;
                    return false;
                } else if (val == l_Undef) {
                    solver->enqueue<false>(subsLits[j]);
                    solver->ok = solver->propagate_occur<false>(simplifier->limit_to_decrease);
                    if (!solver->okay()) {
                        return false;
                    }
                }
                //this binary is definitely satisfied
                solver->detach_bin_clause(
                    subs[j].lit, subs[j].ws.lit2(), subs[j].ws.red(), subs[j].ws.get_ID());
                (*solver->frat) << del << subs[j].ws.get_ID() << subs[j].lit << subs[j].ws.lit2() << fin;
                if (!subs[j].ws.red()) {
                    simplifier->n_occurs[subs[j].lit.toInt()]--;
                    simplifier->n_occurs[subs[j].ws.lit2().toInt()]--;
                    simplifier->elim_calc_need_update.touch(subs[j].lit);
                    simplifier->elim_calc_need_update.touch(subs[j].ws.lit2());
                    simplifier->removed_cl_with_var.touch(subs[j].lit);
                    simplifier->removed_cl_with_var.touch(subs[j].ws.lit2());
                }
            }
            continue;
        }

        assert(subs[j].ws.isClause());
        ClOffset offset2 = subs[j].ws.get_offset();
        Clause& cl2 = *solver->cl_alloc.ptr(offset2);
        if (subsLits[j] == lit_Undef) {  //Subsume
            #ifdef VERBOSE_DEBUG
            if (solver->conf.verbosity >= 6)
                cout << "subsumed clause " << cl2 << endl;
            #endif
            if (cl2.used_in_xor() &&
                solver->conf.force_preserve_xors)
            {
                continue;
            }

            if (!cl2.red()) {
                ret_sub_str.subsumedIrred = true;
            }

            simplifier->unlink_clause(offset2, true, false, true);
            ret_sub_str.sub++;
        } else { //Strengthen
            #ifdef VERBOSE_DEBUG
            if (solver->conf.verbosity >= 6) {
                cout << "strenghtened clause " << cl2 << endl;
            }
            #endif
            if (cl2.used_in_xor() &&
                solver->conf.force_preserve_xors)
            {
                //cout << "str-ing used in XOR with bin" << endl;
                continue;
            }
            if (!simplifier->remove_literal(offset2, subsLits[j], true)) {
                return false;
            }
            ret_sub_str.str++;

            //If we are waaay over time, just exit
            if (*simplifier->limit_to_decrease < -20LL*1000LL*1000LL)
                break;
        }
    }
    runStats.sub1 += ret_sub_str;
    return true;
}

//Implicit input here is ALWAYS irred
void SubsumeStrengthen::backw_sub_with_impl(
    const vector<Lit>& lits,
    Sub1Ret& ret_sub_str
) {
    subs.clear();

    find_subsumed(
        CL_OFFSET_MAX
        , lits
        , calcAbstraction(lits)
        , subs
        , true
    );

    for (size_t j = 0
        ; j < subs.size() && solver->okay()
        ; j++
    ) {
        if (subs[j].ws.isBin()) {
            remove_binary_cl(subs[j]);
            continue;
        }

        assert(subs[j].ws.isClause());
        ClOffset offset2 = subs[j].ws.get_offset();
        Clause& cl2 = *solver->cl_alloc.ptr(offset2);
        if (subsLits[j] == lit_Undef) {  //Subsume
            if (cl2.used_in_xor() && solver->conf.force_preserve_xors)
                continue;

            if (!cl2.red()) ret_sub_str.subsumedIrred = true;
            simplifier->unlink_clause(offset2, true, false, true);
            ret_sub_str.sub++;
        }
    }
    runStats.sub1 += ret_sub_str;
}

bool SubsumeStrengthen::backw_sub_str_long_with_bins_watch(
    const Lit lit,
    bool both_bins
) {
    //NOTE this can modify itself,
    //     by removing a binary from tmp by backw_sub_str_with_impl
    solver->watches[lit].copyTo(tmp);
    for (size_t i = 0
        ; i < tmp.size() && *simplifier->limit_to_decrease > 0
        ; i++
    ) {
        //Each BIN only once
        if (tmp[i].isBin() &&
            (both_bins || lit < tmp[i].lit2()))
        {
            const bool red = tmp[i].red();
            tried_bin_tri++;
            tmpLits.resize(2);
            tmpLits[0] = lit;
            tmpLits[1] = tmp[i].lit2();
            std::sort(tmpLits.begin(), tmpLits.end());

            Sub1Ret ret;
            if (!backw_sub_str_with_impl(tmpLits, ret)) {
                return false;
            }
            subsumedBin += ret.sub;
            strBin += ret.str;

            if (red
                && ret.subsumedIrred
            ) {
                solver->binTri.redBins--;
                solver->binTri.irredBins++;
                simplifier->n_occurs[tmpLits[0].toInt()]++;
                simplifier->n_occurs[tmpLits[1].toInt()]++;
                simplifier->elim_calc_need_update.touch(tmpLits[0]);
                simplifier->elim_calc_need_update.touch(tmpLits[1]);
                simplifier->added_cl_to_var.touch(tmpLits[0]);
                simplifier->added_cl_to_var.touch(tmpLits[1]);
                findWatchedOfBin(
                    solver->watches, tmpLits[1], tmpLits[0], true, tmp[i].get_ID()).setRed(false);
                findWatchedOfBin(
                    solver->watches, tmpLits[0], tmpLits[1], true, tmp[i].get_ID()).setRed(false);
            }
            continue;
        }

        //Must be a longer clause, break
        //assert(ws[i].isClause());
        //break;
    }

    return true;
}

bool SubsumeStrengthen::backw_sub_str_long_with_bins()
{
    //Stats
    int64_t orig_time_limit = *simplifier->limit_to_decrease;
    const size_t origTrailSize = solver->trail_size();
    double myTime = cpuTime();
    subsumedBin = 0;
    strBin = 0;

    //Randomize start in the watchlist
    size_t upI;
    upI = rnd_uint(solver->mtrand, solver->watches.size()-1);

    size_t numDone = 0;
    for (; numDone < solver->watches.size() && *simplifier->limit_to_decrease > 0
        ; upI = (upI +1) % solver->watches.size(), numDone++

    ) {
        Lit lit = Lit::toLit(upI);
        if (!backw_sub_str_long_with_bins_watch(lit)) {
            break;
        }
    }

    const double time_used = cpuTime() - myTime;
    const bool time_out = *simplifier->limit_to_decrease <= 0;
    const double time_remain = float_div(*simplifier->limit_to_decrease, orig_time_limit);
    if (solver->conf.verbosity) {
        cout
        << "c [occ-backw-sub-str-long-w-bins]"
        << " subs: " << subsumedBin
        << " str: " << strBin
        << " tried: " << tried_bin_tri
        << " 0-depth ass: " << solver->trail_size() - origTrailSize
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }

    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "occ-backw-sub-str-long-w-bins"
            , time_used
            , time_out
            , time_remain
        );
    }

    //runStats.zeroDepthAssigns = solver->trail_size() - origTrailSize;

    return solver->okay();
}


void SubsumeStrengthen::finishedRun()
{
    globalstats += runStats;
}

void SubsumeStrengthen::Stats::print_short(const Solver* solver) const
{
    cout << "c [occ-substr] long"
    << " subBySub: " << sub0.numSubsumed
    << " subByStr: " << sub1.sub
    << " lits-rem-str: " << sub1.str
    << solver->conf.print_times(subsumeTime+strengthenTime)
    << endl;
}

void SubsumeStrengthen::Stats::print() const
{
    cout << "c -------- SubsumeStrengthen STATS ----------" << endl;
    print_stats_line("c cl-subs"
        , sub0.numSubsumed + sub1.sub
        , " Clauses"
    );
    print_stats_line("c cl-str rem lit"
        , sub1.str
        , " Lits"
    );
    print_stats_line("c cl-sub T"
        , subsumeTime
        , " s"
    );
    print_stats_line("c cl-str T"
        , strengthenTime
        , " s"
    );
    cout << "c -------- SubsumeStrengthen STATS END ----------" << endl;
}

SubsumeStrengthen::Stats& SubsumeStrengthen::Stats::operator+=(const Stats& other)
{
    sub1 += other.sub1;
    sub0 += other.sub0;

    subsumeTime += other.subsumeTime;
    strengthenTime += other.strengthenTime;

    return *this;
}
