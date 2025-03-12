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

#ifndef __SQLSTATS_H__
#define __SQLSTATS_H__

#include "searchstats.h"
#include "vardata.h"
#include "searchhist.h"

#ifdef STATS_NEEDED
#include "satzilla_features.h"
#endif

namespace CMSat {

class Solver;
class Searcher;
class Clause;

class SQLStats
{
public:

    virtual ~SQLStats();

    virtual void end_transaction() = 0;
    virtual void begin_transaction() = 0;

    virtual void time_passed(
        const Solver* solver
        , const string& name
        , double time_passed
        , bool time_out
        , double percent_time_remain
    ) = 0;

    virtual void time_passed_min(
        const Solver* solver
        , const string& name
        , double time_passed
    ) = 0;

    virtual void mem_used(
        const Solver* solver
        , const string& name
        , const double given_time
        , uint64_t mem_used_mb
    ) = 0;

    virtual void set_id_confl(
        const int32_t id
        , const uint64_t sumConflicts
    ) = 0;

    #ifdef STATS_NEEDED
    virtual void satzilla_features(
        const Solver* solver
        , const Searcher* search
        , const SatZillaFeatures& satzilla_feat
    ) = 0;

    virtual void restart(
        const uint32_t restartID
        , const Restart rest_type
        , const PropStats& thisPropStats
        , const SearchStats& thisStats
        , const Solver* solver
        , const Searcher* searcher
        , const rst_dat_type type
        , const int64_t clauseID = -1
    ) = 0;

    virtual void reduceDB(
        const Solver* solver
        , const bool locked
        , const Clause* cl
        , const uint32_t reduceDB_called
    ) = 0;

    virtual void reduceDB_common(
        const Solver* solver,
        const uint32_t reduceDB_called,
        const uint32_t tot_cls_in_db,
        const uint32_t cur_rst_type,
        const MedianCommonDataRDB& median_data,
        const AverageCommonDataRDB& avg_data
    ) = 0;

    #ifdef STATS_NEEDED_BRANCH
    virtual void var_data_picktime(
        const Solver* solver
        , const uint32_t var
        , const VarData& vardata
        , const double rel_activity
    ) = 0;

    virtual void var_data_fintime(
        const Solver* solver
        , const uint32_t var
        , const VarData& vardata
        , const double rel_activity
    ) = 0;

    virtual void dec_var_clid(
        const uint32_t var
        , const uint64_t sumConflicts_at_picktime
        , const uint64_t clid
    ) = 0;

    virtual void var_dist(
        const uint32_t var
        , const VarData2& data
        , const Solver* solver
    ) = 0;
    #endif

    virtual void cl_last_in_solver(
        const Solver* solver
        , const uint64_t clid
    ) = 0;

    virtual void update_id(
        const uint32_t old_id
        , const uint32_t new_id
    ) = 0;

    virtual void clause_stats(
        const Solver* solver
        , uint64_t clid
        , uint64_t restartID
        , uint32_t glue
        , uint32_t glue_before_minim
        , uint32_t size
        , uint32_t size_before_minim
        , uint32_t backtrack_level
        , AtecedentData<uint16_t> resoltypes
        , size_t decision_level
        , size_t trail_depth
        , uint64_t conflicts_this_restart
        , const uint32_t restart_type
        , const SearchHist& hist
        , const bool is_decision
        , const uint32_t orig_connects_num_communities
    ) = 0;
    #endif

    virtual bool setup(const Solver* solver) = 0;
    virtual void finishup(lbool status) = 0;
    virtual void add_tag(const std::pair<std::string, std::string>& tag) = 0;
};

} //end namespace

#endif //__SQLSTATS_H__
