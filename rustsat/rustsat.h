#include <cstdarg>
#include <cstdint>
#include <cstdlib>
#include <ostream>
#include <new>

enum class MaybeError {
  /// No error
  Ok,
  /// Encode was not called before using the encoding
  NotEncoded,
  /// The requested encoding is unsatisfiable
  Unsat,
};

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is based on a node database.
/// For now, this implementation only supports upper bounding.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
struct DbTotalizer;

/// Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
///
/// **Note**:
/// This implementation of the  DPW encoding only supports incrementally
/// changing the bound, but not adding new input literals. Calling extend after
/// encoding resets the entire encoding and with the next encode and entirely
/// new encoding will be returned.
///
/// ## References
///
/// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
struct DynamicPolyWatchdog;

using CVarManager = int(*)();

using CClauseCollector = void(*)(int lit, void *data);

using CAssumpCollector = void(*)(int lit, void *data);

extern "C" {

/// Creates a new [`DbTotalizer`] cardinality encoding
DbTotalizer *tot_new();

/// Adds a new input literal to a [`DbTotalizer`]
void tot_add(DbTotalizer *tot, int lit);

/// Lazily builds the _change in_ cardinality encoding to enable upper
/// bounds in a given range. A change might be added literals or changed
/// bounds.
///
/// The min and max bounds are inclusive. After a call to
/// [`tot_encode_ub`] with `min_bound=2` and `max_bound=4` bound
/// including `<= 2` and `<= 4` can be enforced.
///
/// A call to `var_manager` must yield a new variable. The
/// encoding will be returned via the given callback function as
/// 0-terminated clauses (in the same way as IPASIR's `add`).
void tot_encode_ub(DbTotalizer *tot,
                   uintptr_t min_bound,
                   uintptr_t max_bound,
                   CVarManager var_manager,
                   CClauseCollector collector,
                   void *collector_data);

/// Returns an assumption/unit for enforcing an upper bound (`sum of
/// lits <= ub`). Make sure that [`tot_encode_ub`] has been called
/// adequately and nothing has been called afterwards, otherwise
/// [`MaybeError::NotEncoded`] will be returned.
MaybeError tot_enforce_ub(DbTotalizer *tot, uintptr_t ub, int *assump);

/// Frees the memory associated with a [`DbTotalizer`]
void tot_drop(DbTotalizer *tot);

/// Creates a new [`DynamicPolyWatchdog`] cardinality encoding
DynamicPolyWatchdog *dpw_new();

/// Adds a new input literal to a [`DynamicPolyWatchdog`]
void dpw_add(DynamicPolyWatchdog *dpw, int lit, uintptr_t weight);

/// Lazily builds the _change in_ pseudo-boolean encoding to enable
/// upper bounds from within the range. A change might only be a change
/// in bounds, the [`DynamicPolyWatchdog`] does not support adding
/// literals at the moment.
///
/// The min and max bounds are inclusive. After a call to
/// [`dpw_encode_ub`] with `min_bound=2` and `max_bound=4` bound
/// including `<= 2` and `<= 4` can be enforced.
///
/// A call to `var_manager` must yield a new variable. The
/// encoding will be returned via the given callback function as
/// 0-terminated clauses (in the same way as IPASIR's `add`).
void dpw_encode_ub(DynamicPolyWatchdog *dpw,
                   uintptr_t min_bound,
                   uintptr_t max_bound,
                   CVarManager var_manager,
                   CClauseCollector collector,
                   void *collector_data);

/// Returns assumptions/units for enforcing an upper bound (`sum of lits
/// <= ub`). Make sure that [`dpw_encode_ub`] has been called adequately
/// and nothing has been called afterwards, otherwise
/// [`MaybeError::NotEncoded`] will be returned.
///
/// Assumptions are returned via the collector callback. There is _no_
/// terminating zero, all assumptions are passed when [`dpw_enforce_ub`]
/// returns.
MaybeError dpw_enforce_ub(DynamicPolyWatchdog *dpw,
                          uintptr_t ub,
                          CAssumpCollector collector,
                          void *collector_data);

/// Frees the memory associated with a [`DynamicPolyWatchdog`]
void dpw_drop(DynamicPolyWatchdog *dpw);

} // extern "C"
