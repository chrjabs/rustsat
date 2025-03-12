// SharpSAT-TD is a modification of SharpSAT (MIT License, 2019 Marc Thurley).
//
// SharpSAT-TD -- Copyright (c) 2021 Tuukka Korhonen
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE
// OR OTHER DEALINGS IN THE SOFTWARE.

#pragma once

#include <iostream>
#include "utils.h"
/* #define DEBUG_ORACLE_VERB */

#ifdef DEBUG_ORACLE_VERB
#define oclv(x) do {cout << x << endl;} while(0)
#define oclv2(x) do {cout << x;} while(0)
#else
#define oclv(x) do {} while(0)
#define oclv2(x) do {} while(0)
#endif

namespace sspp {
namespace oracle {

struct TriState {
    TriState() {}

    TriState(bool _b) {
        if (_b) val = 1;
        else val = 0;
    }

    static TriState unknown() {
        TriState tmp;
        tmp.val = 2;
        return tmp;
    }

    bool isTrue() const {return val == 1;}
    bool isFalse() const {return val == 0;}
    bool isUnknown() const {return val == 2;}
    int val;
};

struct Stats {
 	int64_t mems = 0;
 	int64_t decisions = 0;
 	int64_t learned_clauses = 0;
 	int64_t learned_bin_clauses = 0;
 	int64_t learned_units = 0;
 	int64_t conflicts = 0;
 	int64_t nontriv_redu = 0;
 	int64_t forgot_clauses = 0;
 	int64_t restarts = 0;
    int64_t cache_useful = 0;
    int64_t cache_added = 0;
  void Print() const;
};

struct Watch {
	// should align to 8+4+4=16 bytes
	size_t cls;
	Lit blit; // blocked literal
	int size;
};

struct VarC {
	size_t reason = 0;
	int level = 0;
	char phase = 0;
};

struct CInfo {
	size_t pt;
	int glue;
	int used;
    uint32_t total_used;
	bool Keep() const;
};

class Oracle {
 public:
  Oracle(int vars_, const vector<vector<Lit>>& clauses_);
  Oracle(int vars_, const vector<vector<Lit>>& clauses_, const vector<vector<Lit>>& learned_clauses_);

  void SetAssumpLit(Lit lit, bool freeze);
  void SetVerbosity(uint32_t _verb) { verb=_verb;}
  TriState Solve(const vector<Lit>& assumps, bool usecache=true, int64_t max_mems = 1000ULL*1000LL*1000LL);
  bool FreezeUnit(Lit unit);
  bool AddClauseIfNeededAndStr(vector<Lit> clause, bool entailed);
  void AddClause(const vector<Lit>& clause, bool entailed);
  void PrintStats() const;
  vector<vector<Lit>> GetLearnedClauses() const;

  int CurLevel() const;
  int LitVal(Lit lit) const;
  const Stats& getStats() const {return stats;}

 private:
    uint32_t verb = 0;
    size_t total_confls = 0;
    size_t last_db_clean = 0;

 	void AddOrigClause(vector<Lit> clause, bool entailed);
 	vector<Lit> clauses;
 	vector<vector<Watch>> watches;
 	vector<signed char> lit_val;
 	vector<VarC> vs;

 	bool unsat = false;

 	const int vars;
 	size_t orig_clauses_size = 0;
 	Stats stats;
 	vector<Lit> prop_q;
 	vector<Var> decided;
 	vector<char> in_cc;

 	std::mt19937 rand_gen;

 	int64_t redu_it = 1;
 	vector<char> seen;
 	vector<int64_t> redu_seen;
 	vector<Lit> redu_s;

 	int64_t lvl_it = 1;
 	vector<int64_t> lvl_seen; // for computing LBD

 	vector<Lit> learned_units;

 	int restart_factor = 0;
 	vector<int> luby;
 	void InitLuby();
 	int NextLuby();

    size_t num_lbd2_red_cls = 0;
    size_t num_used_red_cls = 0;
 	void ResizeClauseDb();
 	void BumpClause(size_t cls);
 	vector<CInfo> cla_info;

 	double var_inc = 1;
 	double var_fact = 0;
 	size_t heap_N;
 	vector<double> var_act_heap;
 	void BumpVar(Var v);
 	void ActivateActivity(Var v);
 	Var PopVarHeap();

 	bool LitSat(Lit lit) const;
 	bool LitAssigned(Lit lit) const;
 	void Assign(Lit dec, size_t reason_clause, int level);
 	void Decide(Lit dec, int level);
 	void UnDecide(int level);

 	TriState HardSolve(int64_t max_mems = 1000LL*1000LL*1000LL);
 	// True if conflict
 	size_t Propagate(int level);

 	size_t AddLearnedClause(const vector<Lit>& clause);
 	bool LitReduntant(Lit lit);
 	void PopLit(vector<Lit>& clause, int& confl_levels, int& impl_lits, int level);
 	vector<Lit> LearnUip(size_t conflict_clause);
 	int CDCLBT(size_t confl_clause, int min_level=0);

 	vector<vector<char>> sol_cache; // Caches found FULL solutions
 	void AddSolToCache();
 	bool SatByCache(const vector<Lit>& assumps) const;
 	void ClearSolCache();
};


inline int Oracle::LitVal(Lit lit) const {
	return lit_val[lit];
}

inline bool Oracle::LitSat(Lit lit) const {
	return LitVal(lit) > 0;
}

inline bool Oracle::LitAssigned(Lit lit) const {
	return LitVal(lit) != 0;
}

// TOP level is 1.
inline int Oracle::CurLevel() const {
	if (decided.empty()) {
		return 1;
	}
	return vs[decided.back()].level;
}

inline void Oracle::Decide(Lit dec, int level) {
	assert(LitVal(dec) == 0);
	stats.decisions++;
	Assign(dec, 0, level);
}

inline void Oracle::AddClause(const vector<Lit>& clause, bool entailed) {
	AddOrigClause(clause, entailed);
}

inline void Oracle::PrintStats() const {
	stats.Print();
}

inline bool CInfo::Keep() const {
	return glue <= 2;
}

} // namespace oracle
} // namespace sspp
