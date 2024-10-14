namespace CaDiCaL {

int64_t Solver::propagations() const {
  TRACE("propagations");
  REQUIRE_VALID_STATE();
  int64_t res = internal->stats.propagations.search;
  LOG_API_CALL_RETURNS("propagations", res);
  return res;
}

int64_t Solver::decisions() const {
  TRACE("decisions");
  REQUIRE_VALID_STATE();
  int64_t res = internal->stats.decisions;
  LOG_API_CALL_RETURNS("decisions", res);
  return res;
}

int64_t Solver::conflicts() const {
  TRACE("conflicts");
  REQUIRE_VALID_STATE();
  int64_t res = internal->stats.conflicts;
  LOG_API_CALL_RETURNS("conflicts", res);
  return res;
}

// Propagate and check
// This is based on the implementation in PySat
// https://github.com/pysathq/pysat/blob/master/solvers/patches/cadical195.patch
bool Solver::prop_check(const int *assumps, size_t assumps_len, bool psaving,
                        void (*prop_cb)(void *, int), void *cb_data) {
  if (internal->unsat || internal->unsat_constraint) {
    return false;
  }

  // saving default options
#ifdef ILB
  int old_ilb = internal->opts.ilb;
#endif
#ifdef REIMPLY
  int old_reimply = internal->opts.reimply;
#endif
  int old_psave = internal->opts.rephase;
  int old_lucky = internal->opts.lucky;
  int old_resall = internal->opts.restoreall;

  // resetting the above options
#ifdef ILB
  internal->opts.ilb = 0;
#endif
#ifdef REIMPLY
  internal->opts.reimply = 0;
#endif
  internal->opts.lucky = psaving;
  internal->opts.rephase = psaving;
  internal->opts.restoreall = 2;

  int tmp = internal->already_solved();
  if (!tmp)
    tmp = internal->restore_clauses();
  if (tmp) {
    // restoring default option values
#ifdef ILB
    internal->opts.ilb = old_ilb;
#endif
#ifdef REIMPLY
    internal->opts.reimply = old_reimply;
#endif
    internal->opts.lucky = old_lucky;
    internal->opts.rephase = old_psave;
    internal->opts.restoreall = old_resall;
    internal->reset_solving();
    internal->report_solving(tmp);
    return false;
  }
  internal->opts.restoreall = old_resall;

  bool unsat = false;
  int level = internal->level;
  bool noconfl = true;
  Clause *old_conflict = internal->conflict;

  // propagate each assumption at a new decision level
  for (size_t i = 0; !unsat && noconfl && i < assumps_len; ++i) {
    int p = assumps[i];

    // deciding
    const signed char tmp = internal->val(p);
    if (tmp < 0) // if assumption is already set to false
      unsat = true;
    else {
#ifdef IPASIRUP
      if (tmp > 0) {
        // add pseudo decision level
#ifdef ILB
        internal->new_trail_level(0);
#else
        internal->level++;
        internal->control.push_back(Level(0, internal->trail.size()));
#endif
        internal->notify_decision();
      } else
        internal->search_assume_decision(p);

      noconfl = internal->propagate();
      if (noconfl)
        noconfl = internal->external_propagate();
#else
      if (tmp == 0) {
        internal->search_assume_decision(p);
        noconfl = internal->propagate();
      }
#endif
    }
  }

  // copy results
  if (internal->level > level) {
    for (size_t i = internal->control[level + 1].trail;
         i < internal->trail.size(); ++i) {
      prop_cb(cb_data, internal->trail[i]);
    }
    // if there is a conflict, push the conflicting literal as well
    if (!noconfl) {
      literal_iterator conflict_ptr = internal->conflict->begin();
      int conflict_val = *conflict_ptr;
      prop_cb(cb_data, conflict_val);
    }
    // backtrack
    internal->backtrack(level);
  }

#ifdef ILB
  internal->opts.ilb = old_ilb;
#endif
#ifdef REIMPLY
  internal->opts.reimply = old_reimply;
#endif

  // restore phase saving
  internal->opts.rephase = old_psave;
  internal->opts.lucky = old_lucky;
  // reset conflict
  internal->conflict = old_conflict;
  internal->reset_solving();
  internal->report_solving(tmp);

  return !unsat && noconfl;
}

} // namespace CaDiCaL
