#ifdef __cplusplus
extern "C" {
#endif

#include <stddef.h>

#include "ccadical.h"

// Struct defining all necessary callback for an external propagator
// None of the callbacks is allowed to be `NULL`
// For all callbacks, the first void pointer argument is what was passed to the
// init function
typedef struct {
  // Notify the propagator about assignments to observed variables.
  // The notification is not necessarily eager. It usually happens before
  // the call of propagator callbacks and when a driving clause is leading
  // to an assignment.
  //
#ifdef OLD_IPASIRUP
  void (*notify_assignment)(void *, int, int);
#else
  void (*notify_assignment)(void *, const int *, size_t);
#endif
  void (*notify_new_decision_level)(void *);
  void (*notify_backtrack)(void *, size_t);

  // Check by the external propagator the found complete solution (after
  // solution reconstruction). If it returns false, the propagator must
  // provide an external clause during the next callback.
  //
  int (*cb_check_found_model)(void *, const int *, size_t);

  // Ask the external propagator for the next decision literal. If it
  // returns 0, the solver makes its own choice.
  //
  int (*cb_decide)(void *);

  // Ask the external propagator if there is an external propagation to make
  // under the current assignment. It returns either a literal to be
  // propagated or 0, indicating that there is no external propagation under
  // the current assignment.
  //
  int (*cb_propagate)(void *);

  // Ask the external propagator for the reason clause of a previous
  // external propagation step (done by cb_propagate). The clause must be
  // added literal-by-literal closed with a 0. Further, the clause must
  // contain the propagated literal.
  //
  int (*cb_add_reason_clause_lit)(void *, int);

  // The following two functions are used to add external clauses to the
  // solver during the CDCL loop. The external clause is added
  // literal-by-literal and learned by the solver as an irredundant
  // (original) input clause. The clause can be arbitrary, but if it is
  // root-satisfied or tautology, the solver will ignore it without learning
  // it. Root-falsified literals are eagerly removed from the clause.
  // Falsified clauses trigger conflict analysis, propagating clauses
  // trigger propagation. In case chrono is 0, the solver backtracks to
  // propagate the new literal on the right decision level, otherwise it
  // potentially will be an out-of-order assignment on the current level.
  // Unit clauses always (unless root-satisfied, see above) trigger
  // backtracking (independently from the value of the chrono option and
  // independently from being falsified or satisfied or unassigned) to level
  // 0. Empty clause (or root falsified clause, see above) makes the problem
  // unsat and stops the search immediately. A literal 0 must close the
  // clause.
  //
  // The external propagator indicates that there is a clause to add.
  //
  // NOTE: pre version 2.1.0 the second input parameter will be ignored
  int (*cb_has_external_clause)(void *, int *);

  // The actual function called to add the external clause.
  //
  int (*cb_add_external_clause_lit)(void *);
} CCaDiCaLExternalPropagatorCallbacks;

// Add call-back which allows to learn, propagate and backtrack based on
// external constraints. Only one external propagator can be connected
// and after connection every related variables must be 'observed' (use
// 'add_observed_var' function).
// Disconnection of the external propagator resets all the observed
// variables.
//
//   require (VALID)
//   ensure (VALID)
//
void ccadical_connect_external_propagator(CCaDiCaL *, void *,
                                          CCaDiCaLExternalPropagatorCallbacks,
                                          int lazy, int forgettable_reasons);
// Returns the data pointer of the propagator
void ccadical_disconnect_external_propagator(CCaDiCaL *);

// Mark as 'observed' those variables that are relevant to the external
// propagator. External propagation, clause addition during search and
// notifications are all over these observed variables.
// A variable can not be observed witouth having an external propagator
// connected. Observed variables are "frozen" internally, and so
// inprocessing will not consider them as candidates for elimination.
// An observed variable is allowed to be a fresh variable and it can be
// added also during solving.
//
//   require (VALID_OR_SOLVING)
//   ensure (VALID_OR_SOLVING)
//
void ccadical_add_observed_var(CCaDiCaL *, int var);

// Removes the 'observed' flag from the given variable. A variable can be
// set unobserved only between solve calls, not during it (to guarantee
// that no yet unexplained external propagation involves it).
//
//   require (VALID)
//   ensure (VALID)
//
void ccadical_remove_observed_var(CCaDiCaL *, int var);

// Removes all the 'observed' flags from the variables. Disconnecting the
// propagator invokes this step as well.
//
//   require (VALID)
//   ensure (VALID)
//
void ccadical_reset_observed_vars(CCaDiCaL *);

// Get reason of valid observed literal (true = it is an observed variable
// and it got assigned by a decision during the CDCL loop. Otherwise:
// false.
//
//   require (VALID_OR_SOLVING)
//   ensure (VALID_OR_SOLVING)
//
int ccadical_is_decision(CCaDiCaL *, int lit);

#ifdef __cplusplus
}
#endif
