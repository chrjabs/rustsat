#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <stack>
#include <vector>

//--------------------------------------------------------------------------//
// Some example implementations of the ExternalPropagator class are shown
// here. In these examples we solve pigeonhole-type SAT problems by
// assigning exactly p_limit pigeons to n holes, such that each hole
// contains at most one pigeon and each pigeon belongs to exactly one hole.
// If p_limit > n, the problem is UNSAT; if p_limit <= n, it is SAT.
// However, note that PHP is NOT a kind of SAT problem where external
// propagation is expected to be helpful, since the complete encoding is
// rather small (so there is no benefit from lazy constraint generation).
// Nevertheless, we use this problem here to keep the example relatively
// simple and avoid implementing complicated domain-specific propagators.

// The main purpose of these examples is to demonstrate certain erroneous
// usage scenarios and highlight some common pitfalls (see 'Fatal error'
// comments). The implementation is simplified and provided as-is, without
// warranty or guarantee to fit for any specific purpose beyond testing and
// demonstration.

static int n = 3;
int p_limit = n;

static int ph (int p, int h) {
  assert (0 <= p), assert (p < p_limit);
  assert (0 <= h), assert (h < n);
  return p * n + h + 1;
}

static int p_id (int lit) { return int ((abs (lit) - 1) / n); }

static int h_id (int lit) { return ((abs (lit) - 1) % n); }

static void formula (CaDiCaL::Solver &solver) {
  // At most one pigeon per hole
  for (int h = 0; h < n; h++)
    for (int p1 = 0; p1 < p_limit; p1++)
      for (int p2 = p1 + 1; p2 < p_limit; p2++)
        solver.add (-ph (p1, h)), solver.add (-ph (p2, h)), solver.add (0);

  // At least one hole per pigeon
  for (int p = 0; p < p_limit; p++) {
    for (int h = 0; h < n; h++)
      solver.add (ph (p, h));
    solver.add (0);
  }
}

static void partial_formula (CaDiCaL::Solver &solver) {
  // At least one hole per pigeon
  for (int p = 0; p < p_limit; p++) {
    for (int h = 0; h < n; h++)
      solver.add (ph (p, h));
    solver.add (0);
  }

  // In this encoding the at most one pigeon per hole constraints will be
  // checked and enforced dynamically in the external propagator
  // (see ActivePropagator).
}

/*----------------------------------------------------------------------------*/
//
// ObserverPropagator:
//
// This class implements a very simple ExternalPropagator that only reports
// the called IPASIR-UP functions with their arguments, without any actual
// interactions with the solver.
//
// The code includes several "Fatal error" scenarios in comments to
// demonstrate possible invalid uses of the interface. These commands can be
// compiled, but will trigger a runtime error during solving.
//
class ObserverPropagator : CaDiCaL::ExternalPropagator,
                           CaDiCaL::FixedAssignmentListener {
  CaDiCaL::Solver *solver;
  // Used to demonstrate forced backtrack
  bool first_model = true;

  // Used to show add_observed_var during cb_propagate
  size_t propagation_count = 0;

  int non_observed_lit = 0;
  int fixed_lit = 0;

public:
  ObserverPropagator (CaDiCaL::Solver *s) : solver (s) {
    // In case the following flag is true, the solver will invoke only the
    // cb_check_found_model callback, without any additional callbacks or
    // notifications. This can be useful for example in model enumeration
    // tasks, or for very lazy propagators where only the final complete
    // solution is planned to be checked.
    //
    // The flag can be changed during solving, however switching it from
    // true to false will mean that the propagator does not know what is the
    // actual state of the trail in the solver (so it is not really
    // recommended).
    is_lazy = false;

    // The following flag determines if the solver is allowed to forget
    // those clauses that are given through the 'cb_add_reason_clause_lit'
    // callback. If the propagator does not use cb_propagate, the value of
    // this flag is irrelevant.
    //
    // The flag can be changed anytime, it is checked before learning each
    // external reason clause.
    are_reasons_forgettable = false;

    // Fatal error: can not observe variables without a connected propagator
    // solver->add_observed_var(1);

    solver->connect_external_propagator (this);

    // In case it is important to know when an assignment is fixed (i.e.,
    // when it is guaranteed to have the assigned value in any found model),
    // the propagator needs to implement the 'FixedAssignmentListener'
    // interface and needs to be connected as a listener as well. It is
    // recommended to connect the FixedAssignmentListener before the formula
    // is given to the solver. Note that the FixedAssignmentListener
    // interface reports every fixed assignments, not just the ones over
    // observed variables. See also the 'notify_fixed_assignment' function.
    solver->connect_fixed_listener (this);

    // Fatal error: can not connect more than one propagator
    // solver->connect_external_propagator (this);

    std::cout
        << "[obs-prop] ObserverPropagator is created and connected "
        << "both as an ExternalPropagator and as a FixedAssignmentListener."
        << std::endl;

    // Fatal error: invalid literal '0'
    // solver->add_observed_var(0);

    for (int h = 0; h < n; h++)
      for (int p = 0; p < p_limit; p++)
        solver->add_observed_var (ph (p, h));

    int max_var = solver->vars ();
    std::cout << "Maximum variable in solver: " << max_var << std::endl;

    int new_var = max_var + 5;
    // Observing a variable before using it in any clause will force the
    // solver to create the variable. Using the solver with factor (BVA)
    // will need to first declare such variables (ask it from the solver)
    // thus it can trigger a fatal error if it is an already existing
    // internal variable. But in this example we have the simplified
    // non-strict interface.
    solver->add_observed_var (new_var);

    // Removing a non-observed (or not even existing) variable has no
    // effect, the solver will not create the variable and will not throw
    // any errors.
    solver->remove_observed_var (new_var + 223);
    assert (solver->vars () < new_var + 223);

    max_var = solver->vars ();
    std::cout << "New maximum variable in solver: " << max_var << std::endl;

    // When a unit clause is found by the SAT solver,
    // notify_fixed_assignment will be immediately called.
    non_observed_lit = new_var - 1;
    fixed_lit = -non_observed_lit;
    solver->clause (-non_observed_lit);
  }

  ~ObserverPropagator () {
    std::cout << "[obs-prop][~ObserverPropagator starts]" << std::endl;

    // Note that disconnecting a propagator will also invoke unobserving
    // every observed variable. In case any of these variables are currently
    // assigned (e.g., because the solver is in a SAT state), it will force
    // the solver to backtrack in order to unassign the variables.
    solver->disconnect_external_propagator ();
    solver->disconnect_fixed_listener ();

    // Fatal error: can not unobserve variables without a connected
    // propagator solver->remove_observed_var (6);

    // Fatal error: can not disconnect propagator without a connected
    // propagator solver->disconnect_external_propagator();

    std::cout << "[obs-prop] ObserverPropagator is disconnected."
              << std::endl;
  }

  // Notification regarding fixed assignments. These assignments are also
  // reported by 'notify_assignment'. However, in case a fixed assignment is
  // done on a higher decision level, the standard external propagator will
  // be notified that it has to be unassigned and then immediately
  // reassigned upon every backtrack to a level higher than 0. Hence,
  // following only the notify_assignment callbacks is correct, but requires
  // more unnecessary work on the propagator side. Using the
  // FixedAssignmentListener notification provides the necessary information
  // to recognize and ignore these notifications in the use cases where it
  // is relevant.
  void notify_fixed_assignment (int lit) {
    std::cout << "[fal][notify_fixed_assignment][" << lit << "]"
              << std::endl;
  }

  // Notification regarding the last batch of assignments made by the
  // solver. All of these assignments are happening in the current decision
  // level and in the order as they appear in lits. But, it is not
  // guaranteed that the very first literal is a decision literal. For
  // example, if the decision literal is unobserved, no notification
  // regarding of its assignment is sent (only that a new level was
  // started). Also, there can happen multiple notifications on the same
  // decision level (consider for example cases where the interaction with
  // the propagator trigger further unit propagation steps in the SAT
  // solver).
  void notify_assignment (const std::vector<int> &lits) {
    std::cout << "[obs-prop][notify_assignment][ ";
    for (const auto lit : lits) {
      std::cout << lit << " ";
    }
    std::cout << "]" << std::endl;
  }

  void notify_new_decision_level () {
    std::cout << "[obs-prop][notify_new_decision_level]" << std::endl;

    // Fatal error: not allowed to force backtrack in that state of the
    // solver solver->force_backtrack(0);
  }

  void notify_backtrack (size_t new_level) {
    std::cout << "[obs-prop][notify_backtrack][ to level " << new_level
              << " ]" << std::endl;

    // Fatal error: not allowed to force backtrack in that state of the
    // solver solver->force_backtrack(0);
  }

  bool cb_check_found_model (const std::vector<int> &model) {
    std::cout << "[obs-prop][cb_check_found_model][ ";
    for (const auto lit : model) {
      std::cout << lit << " ";
    }
    std::cout << "]" << std::endl;

    // In this callback we are allowed to force the solver to backtrack (and
    // thereby throw away the found model). Note however that if backtrack
    // was forced, the return value of this function is ignored by the
    // solver.
    if (first_model) {
      first_model = false;
      solver->force_backtrack (0);
      return true;
    }

    return true;
  }

  int cb_decide () {
    std::cout << "[obs-prop][cb_decide][0]" << std::endl;

    // This is the only other callback (beyond 'cb_check_found_model') where
    // force_backtrack is allowed to be called. However, the argument of
    // this forced backtrack must be a valid decision level. The following
    // calls are triggering fatal API errors:

    // Fatal error: the target level of a forced backtrack must be
    // non-negative. solver->force_backtrack(-6);

    // Fatal error: cadical: the target level of a forced backtrack must be
    // smaller than the current decision level.
    // solver->force_backtrack(n*p_limit+5);

    // Regarding the external decisions, only observed literals over yet
    // unassigned variables are allowed:

    // Fatal error: external decisions are only allowed over observed
    // variables. return non_observed_lit;

    // Fatal error: external decisions are only allowed over unassigned
    // variables. return fixed_lit;

    return 0;
  };

  int cb_propagate () {
    std::cout << "[obs-prop][cb_propagate]";
    propagation_count++;
    // It is not an error if the externally propagated literal is already
    // assigned. In case the new propagation contradicts the assignment, the
    // reason of the propagation is immediately asked and conflict analysis
    // starts. If the new propagation agrees with an already existing
    // internal assignment, the external propagation step has no effect. If
    // the variable is not yet assigned, external propagation will enforce
    // the propagated assignment.

    // Fatal error: not allowed to force backtrack in that state of the
    // solver solver->force_backtrack(0);

    // Fatal error: external propagations are only allowed over observed
    // variables. return non_observed_lit;

    // Here 6 and 7 are just arbitrarily picked numbers to demonstrate some
    // special features of cb_propagate in combination with add_observed_var
    if (propagation_count == 6) {

      // It is allowed to add new observed variables during this callback.
      int fresh_variable = solver->vars () + 1;
      solver->add_observed_var (fresh_variable);

      // It is not necessary to use the newly observed variable in the
      // propagation.
      std::cout << "[0]" << std::endl;
      return 0;

    } else if (propagation_count == 7) {
      std::cout << "[" << -non_observed_lit << "]" << std::endl;
      // In case the newly observed variable is already assigned in the
      // solver, the SAT solver will need to backtrack to undo the
      // corresponding assignment (so that the user can get notified about
      // its value later).
      // Thus, the following command forces the solver to backtrack to level
      // 0 (because this variable was already assigned by the added unit
      // clause in the constructor) and triggers the corresponding
      // 'notify_backtrack' callback at the same time.
      solver->add_observed_var (non_observed_lit);

      // Thus, this external propagation step will take effect on the
      // decision level after backtracking (in this example level 0). So if
      // there are external propagation steps that require to on-the-fly
      // observe already assigned variables, it is important to make sure
      // that the propagation holds even after the SAT solver backtracked
      // (the solver can not check it since the reason of the propagation
      // step is not given here). In general, the safest and easiest
      // approach is to observe any potentially relevant variables from the
      // beginning on and add new observed variables during solving only if
      // they are fresh variables.
      return -non_observed_lit;
    }

    std::cout << "[0]" << std::endl;
    return 0;
  };

  int cb_add_reason_clause_lit (int propagated_lit) {
    (void) propagated_lit;
    // In this example we have no used external propagations, so this
    // function will not be called by the SAT solver.

    // For the possible error scenarios see the ActivePropagator example.

    assert (false);
    return 0;
  };

  bool cb_has_external_clause (bool &is_forgettable) {
    (void) is_forgettable;
    std::cout << "[obs-prop][cb_has_external_clause][no]" << std::endl;

    // Fatal error: not allowed to force backtrack in that state of the
    // solver
    // solver->force_backtrack(0);

    return false;
  }

  int cb_add_external_clause_lit () {
    // In this example we have no external clauses to add (i.e, the function
    // 'cb_has_external_clause' always returns false), so this function
    // will not be called by the SAT solver.

    // For the possible error scenarios see the ActivePropagator example.

    assert (false);
    return 0;
  }
};

// This helper class is used to recognize when an external propagation or
// external falsified clause can be added to the solver. The implementation
// is naiv and simple, but it allows to keep the implementation of the
// ActivePropagator class (see below) simpler.

class AssignmentStatus {
public:
  // Used to recognize if there are yet unassigned variables
  size_t next_unassigned_pos = 0;

  // The actual assignment regarding each object. 1 indicates that the
  // element is selected, 0 indicates unknown (unassigned), and -1 indicates
  // that it is not selected under the current assignment.
  std::vector<int> amap;

  // Number of selected elements
  size_t p_count = 0;

  AssignmentStatus (size_t size) : amap (size, 0) {}

  void reset () {
    amap.assign (amap.size (), 0);
    next_unassigned_pos = 0;
    p_count = 0;
  }

  void assign (size_t pos, int val) {
    assert (!amap[pos]);
    if (val > 0) {
      p_count++;
      amap[pos] = 1;
    } else
      amap[pos] = -1;

    if (next_unassigned_pos == pos) {
      while (++next_unassigned_pos < amap.size () &&
             amap[next_unassigned_pos]) {
      };
    }
  }

  void unassign (size_t pos) {
    assert (amap[pos]);
    if (amap[pos] > 0)
      p_count--;
    amap[pos] = 0;
    if (pos < next_unassigned_pos)
      next_unassigned_pos = pos;
  }

  // The assignment propagates if exactly one element is already selected
  // and there are yet unassigned positions.
  bool propagates () const {
    return (p_count == 1 && next_unassigned_pos < amap.size ());
  }

  // It returns the first selected index (or -1 if there is none)
  int get_val () const {
    for (size_t i = 0; i < amap.size (); i++) {
      if (amap[i] > 0)
        return i;
    }
    return -1;
  }

  // Returns true if there are more than one selected elements
  bool conflicting () const { return (p_count > 1); }
};

/*----------------------------------------------------------------------------*/
//
// ActivePropagator:
//
// This class implements a more complex ExternalPropagator that follows the
// assignment steps of the solver and provides additional propagation steps
// based on the not pre-encoded part of the problem (the at most one pigeon
// per hole constraints).
//
// This example also shows a possible way to schedule the deletion of the
// not used reason clauses of external propagation steps (in case they are
// built upon propagation and not only when asked for them specificly).
class ActivePropagator : CaDiCaL::ExternalPropagator {
private:
  CaDiCaL::Solver *solver;

  // Initially every hole and every pigeons are unassigned
  std::vector<AssignmentStatus> hole_map;
  std::vector<AssignmentStatus> pigeon_map;

  // Since we ignore in this example the out-of-order fixed assignments, the
  // trail is a stack (instead of a deque)
  std::stack<std::vector<int>> observed_trail;

  // Used for storing the current external (reason) clauses during
  // interactions with the solver.
  std::vector<int> clause;
  size_t next_lit = 0;

  // In this example every external propagation is propagated from a binary
  // clause (one assigned pigeon forces each other pigeons to not get
  // assigned to the same hole). We store explicitly the reason literals
  // upon propagation, because recalculating on-the-fly the right reason
  // would require us to track the order of the assignments made.
  std::map<int, int> reason_map;

  // The external propagations that are currently unassigned. Whenever the
  // solver reaches a decision point ('cb_decide'), we can safely delete
  // these reasons from the reason_map.
  std::set<int> unassigned_reasons;

  // Used to demonstrate some illegal use cases.
  int non_observed_lit;

public:
  ActivePropagator (CaDiCaL::Solver *s)
      : solver (s), hole_map (n, p_limit), pigeon_map (p_limit, n) {
    is_lazy = false;

    // In this example we can always cheaply re-add external clauses if
    // necessary, so we allow the SAT solver to consider them during clause
    // database reduction.
    are_reasons_forgettable = true;

    solver->connect_external_propagator (this);

    // This propagator ignores the FixedAssignments and relies only on
    // the standard notification messages (which might report to unassign
    // and then later reassing an actually fixed variable).
    std::cout << "[act-prop] ActivePropagator is created and connected as "
                 "an ExternalPropagator"
              << std::endl;

    // Observe all variables of the encoding
    for (int h = 0; h < n; h++) {
      for (int p = 0; p < n + 1; p++) {
        solver->add_observed_var (ph (p, h));
      }
    }

    non_observed_lit = solver->vars () + 1;
    // Create the root-level of the trail. This level needs to be always
    // there.
    observed_trail.push (std::vector<int> ());
  }

  ~ActivePropagator () {
    std::cout << "[act-prop][~ActivePropagator starts]" << std::endl;

    while (!observed_trail.empty ())
      observed_trail.pop ();

    hole_map.clear ();
    pigeon_map.clear ();

    solver->disconnect_external_propagator ();
    std::cout << "[act-prop] ActivePropagator is disconnected."
              << std::endl;
  }

  void notify_assignment (const std::vector<int> &lits) override {
    // We update the assignment states of the propagator, but in this
    // example we do not check eagerly if there is any possible conflict or
    // propagation (this will be checked only when it is relevant, ie., in
    // 'cb_propagate' and 'cb_has_external_clause').
    std::cout << "[act-prop][notify_assignment][ ";
    for (const auto lit : lits) {
      std::cout << lit << " ";

      // Add the new assignment to the observed trail
      observed_trail.top ().push_back (lit);

      // Update the maps based on the assignment
      int pig_id = p_id (lit);
      int hole_id = h_id (lit);
      hole_map[hole_id].assign (pig_id, lit);
      pigeon_map[pig_id].assign (hole_id, lit);

      // In case it was a previously externally propagated step, this
      // notification of assignment is actually about the reassignment of
      // it, hence we might need the reason clause of it later.
      unassigned_reasons.erase (lit);
    }
    std::cout << "]" << std::endl;
  }

  void notify_new_decision_level () override {
    std::cout << "[act-prop][notify_new_decision_level]" << std::endl;

    // Create a new decision level on the observed trail
    observed_trail.push (std::vector<int> ());
  }

  void notify_backtrack (size_t new_level) override {
    std::cout << "[act-prop][notify_backtrack][ "
              << observed_trail.size () - 1 << " -> " << new_level << " ]"
              << "[unassigned: ";

    // Undo all the backtracked assignments on the observed trail and
    // in the assignment maps.
    while (observed_trail.size () > new_level + 1) {
      for (auto lit : observed_trail.top ()) {
        std::cout << lit << " ";

        int pig_id = p_id (lit);
        int hole_id = h_id (lit);
        hole_map[hole_id].unassign (pig_id);
        pigeon_map[pig_id].unassign (hole_id);

        // In case it was a previously externally propagated literal, we
        // mark the reason clause of it for deletion, but do not delete it
        // yet. See 'notify_assignment' and 'cb_decide' for more details
        // regarding reason storing.
        if (reason_map.find (lit) != reason_map.end ()) {
          unassigned_reasons.insert (lit);
        }
      }
      observed_trail.pop ();
    }
    std::cout << "]" << std::endl;
  }

  bool cb_check_found_model (const std::vector<int> &model) override {
    std::cout << "[act-prop][cb_check_found_model][ ";
    for (const auto lit : model) {
      std::cout << lit << " ";
    }
    std::cout << "]" << std::endl;

    return true;
  }

  int cb_decide () override {
    std::cout << "[act-prop][cb_decide][0]" << std::endl;

    // Here we can erase the reasons of the unassigned externally
    // propagated literals, since it is sure that none of them will be
    // reused (i.e., reassigned) by the SAT solver anymore.

    for (const auto &lit : unassigned_reasons) {
      reason_map.erase (lit);
    }

    return 0;
  };

  int cb_propagate () override {
    std::cout << "[act-prop][cb_propagate]";

    // Check if any of the assignments is propagating. If one found, return.
    // There are use cases where it pays off to detect only when a conflict
    // happens and ignore the individual propagation steps.
    // Another alternative is to only use external proapgations to trigger
    // conflicts (by propagating a falsified literal and then giving its
    // reason clause in the next 'cb_add_reason_clause_lit' callback).
    // In this example we mix both options, first only propagating and
    // then detecting conflicts in the 'has_external_clause' callbacks.

    // See ObserverPropagator example for some potential errornous use
    // cases of 'cb_propagate'.

    for (int h = 0; h < n; h++) {
      if (hole_map[h].propagates ()) {
        int lit = -1 * ph (hole_map[h].next_unassigned_pos, h);
        std::cout << "[" << lit << "]" << std::endl;
        reason_map[lit] = -1 * ph (hole_map[h].get_val (), h);
        return lit;
      }
    }

    for (int p = 0; p < p_limit; p++) {
      if (pigeon_map[p].propagates ()) {
        int lit = -1 * ph (p, pigeon_map[p].next_unassigned_pos);
        std::cout << "[" << lit << "]" << std::endl;
        reason_map[lit] = -1 * ph (p, pigeon_map[p].get_val ());
        return lit;
      }
    }

    std::cout << "[0]" << std::endl;
    return 0;
  };

  void explain_propagation (int propagated_lit) {
    assert (propagated_lit < 0);

    clause.clear ();
    next_lit = 0;

    clause.push_back (propagated_lit);
    clause.push_back (reason_map[propagated_lit]);
    clause.push_back (0);
  }

  int cb_add_reason_clause_lit (int propagated_lit) override {
    // In this example we explicitly saved the reason of every external
    // propagation step in the 'reason_map', so we can simply look it up
    // and construct the necessary clause when required.
    std::cout << "[act-prop][cb_add_reason_clause_lit][" << propagated_lit
              << "][ ";

    // Fatal error: external reason clause must contain the propagated
    // literal. return 0;

    // Fatal error: external (reason) clause must contain only observed
    // variables. return non_observed_lit;

    // Fatal error: solver in invalid state
    // solver->disconnect_external_propagator ();

    if (clause.empty ())
      explain_propagation (propagated_lit);
    assert (next_lit < clause.size ());

    int lit = clause[next_lit++];
    if (!lit) {
      clause.clear ();
      next_lit = 0;
    }

    // Fatal error: can not unobserve assigned variable during conflict
    // analysis if (lit) {
    //   solver->remove_observed_var (abs(lit));
    // }

    std::cout << lit << " ]" << std::endl;
    return lit;
  };

  bool cb_has_external_clause (bool &is_forgettable) override {
    std::cout << "[act-prop][cb_has_external_clause][ ";

    for (int h = 0; h < n; h++) {
      if (hole_map[h].conflicting ()) {

        is_forgettable = true;
        clause.clear ();

        for (int p = 0; p < p_limit; p++) {
          int pid = hole_map[h].amap[p];
          if (pid > 0) {
            int lit = -1 * ph (p, h);
            clause.push_back (lit);
            std::cout << lit << " ";
          }
        }

        clause.push_back (0);
        next_lit = 0;
        std::cout << "]" << std::endl;
        return true;
      }
    }

    for (int p = 0; p < p_limit; p++) {
      if (pigeon_map[p].conflicting ()) {

        is_forgettable = true;
        clause.clear ();

        for (int h = 0; h < n; h++) {
          int hole_val = pigeon_map[p].amap[h];
          if (hole_val > 0) {
            int lit = -1 * ph (p, h);
            clause.push_back (lit);
            std::cout << lit << " ";
          }
        }

        clause.push_back (0);
        next_lit = 0;
        std::cout << "]" << std::endl;
        return true;
      }
    }

    is_forgettable = true;
    clause.clear ();

    std::cout << "no ]" << std::endl;
    return false;
  }

  int cb_add_external_clause_lit () override {
    if (next_lit < clause.size ()) {
      int lit = clause[next_lit++];
      if (!lit) {
        clause.clear ();
        next_lit = 0;
      }
      return lit;
    }

    assert (false);
    return 0;
  }
};

void observer_example () {
  CaDiCaL::Solver solver;

  // We use the simplified interface (so there are no explicit variable
  // declarations)
  solver.set ("factor", 0);

  // Fatal error: can not observe variables without a connected propagator
  // solver.add_observed_var(4);

  p_limit = n; // satisfiable example

  ObserverPropagator observer (&solver);
  formula (solver);

  int res = solver.solve ();
  std::cout << "Result: " << res << std::endl;

  assert (res == 10);
  if (res == 10) {
    std::cout << "s ";
    for (int h = 1; h <= solver.vars (); h++) {
      std::cout << solver.val (h) << " ";
    }
    std::cout << std::endl;
  }
}

void active_propagator_example () {
  CaDiCaL::Solver solver;

  // We use the simplified interface (so there are no explicit variable
  // declarations)
  solver.set ("factor", 0);

  // We generate for this example an unsatisfiable PHP problem.
  p_limit = n + 1;

  ActivePropagator propagator (&solver);

  partial_formula (solver);

  int res = solver.solve ();
  std::cout << "Result: " << res << std::endl;
  assert (res == 20);
}

int main () {
  observer_example ();
  std::cout << "-----------------------------------------------------------"
            << std::endl;
  active_propagator_example ();
  return 0;
}
