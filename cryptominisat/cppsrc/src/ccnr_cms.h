/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file <soos.mate@gmail.com>

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

#ifndef CMS_ccnr_H
#define CMS_ccnr_H

#include <cstdint>
#include <cstdio>
#include <utility>
#include "solvertypes.h"

namespace CCNR {
    class ls_solver;
}

namespace CMSat {

class Solver;
using std::pair;
using std::make_pair;

class CMS_ccnr {
public:
    lbool main(const uint32_t num_sls_called);
    CMS_ccnr(Solver* _solver);
    ~CMS_ccnr();

private:
    Solver* solver;

    /************************************/
    /* Main                             */
    /************************************/
    void flipvar(uint32_t toflip);

    /************************************/
    /* Initialization                   */
    /************************************/
    void parse_parameters();
    void init_for_round();
    bool init_problem();
    lbool deal_with_solution(int res, const uint32_t num_sls_called);
    CCNR::ls_solver* ls_s = NULL;
    uint32_t cl_num = 0;

    enum class add_cl_ret {added_cl, skipped_cl, unsat};
    template<class T>
    add_cl_ret add_this_clause(const T& cl);
    vector<int> yals_lits;
    vector<uint32_t>& seen;
    vector<Lit>& toClear;

    //Bumping of variable scores
    vector<pair<uint32_t, double>> get_bump_based_on_cls();
    vector<pair<uint32_t, double>> get_bump_based_on_var_scores();
    vector<pair<uint32_t, double>> get_bump_based_on_var_flips();
    vector<pair<uint32_t, double>> get_bump_based_on_conflict_ct();
};

}

#endif //CMS_WALKSAT_H
