#ifndef rustsat_h
#define rustsat_h

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#define RUSTSAT_VERSION 0.7.2
#define RUSTSAT_VERSION_MAJOR 0
#define RUSTSAT_VERSION_MINOR 7
#define RUSTSAT_VERSION_PATCH 2

#ifdef __cplusplus
namespace RustSAT {
#endif  // __cplusplus

typedef enum MaybeError {
  /**
   * No error
   */
  Ok = 0,
  /**
   * Encode was not called before using the encoding
   */
  NotEncoded,
  /**
   * The requested encoding is unsatisfiable
   */
  Unsat,
  /**
   * The encoding is in an invalid state to perform this action
   */
  InvalidState,
  /**
   * Invalid IPASIR-style literal
   */
  InvalidLiteral,
  /**
   * Precision divisor is not a power of 2
   */
  PrecisionNotPow2,
  /**
   * Attempting to decrease precision
   */
  PrecisionDecreased,
} MaybeError;

/**
 * Implementation of the bimander at-most-1 encoding.
 *
 * The sub encoding is fixed to the pairwise encoding and the size of the splits to 4.
 *
 * # References
 *
 * - Van-Hau Nguyen and Son Thay Mai: _A New Method to Encode the At-Most-One Constraint into SAT,
 *   SOICT 2015.
 */
typedef struct Bimander Bimander;

/**
 * Implementation of the binary adder encoding first described in \[1\].
 * The implementation follows the description in \[2\].
 *
 * ## References
 *
 * - \[1\] Joose P. Warners: _A linear-time transformation of linear inequalities into conjunctive
 *   normal form_, Inf. Process. Lett. 1998.
 * - \[2\] Niklas Eén and Niklas Sörensson: _Translating Pseudo-Boolean Constraints into SAT_,
 *   JSAT 2006.
 */
typedef struct BinaryAdder BinaryAdder;

/**
 * Implementations of the bitwise at-most-1 encoding.
 *
 * # References
 *
 * - Steven D. Prestwich: _Finding large Cliques using SAT Local Search_, in Trends in Constraint
 *   Programming 2007.
 * - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.
 */
typedef struct Bitwise Bitwise;

/**
 * Implementations of the commander at-most-1 encoding.
 *
 * The sub encoding is fixed to the pairwise encoding and the size of the splits to 4.
 *
 * # References
 *
 * - Will Klieber and Gihwon Kwon: _Efficient CNF Encoding for Selecting 1 from N Objects, CFV
 *   2007.
 */
typedef struct Commander Commander;

/**
 * Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
 *
 * **Note**:
 * This implementation of the  DPW encoding only supports incrementally
 * changing the bound, but not adding new input literals. Calling extend after
 * encoding resets the entire encoding and with the next encode and entirely
 * new encoding will be returned.
 *
 * ## References
 *
 * - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
 *   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
 */
typedef struct DynamicPolyWatchdog DynamicPolyWatchdog;

/**
 * Implementation of the binary adder tree generalized totalizer encoding
 * \[1\]. The implementation is incremental. The implementation is recursive.
 * This encoding only support upper bounding. Lower bounding can be achieved by
 * negating the input literals. This is implemented in
 * [`super::simulators::Inverted`].
 * The implementation is based on a node database.
 *
 * # References
 *
 * - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
 *   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
 */
typedef struct GeneralizedTotalizer GeneralizedTotalizer;

/**
 * Implementations of the ladder at-most-1 encoding.
 *
 * # References
 *
 * - Ian P. Gent and Peter Nightingale: _A new Encoding of AllDifferent into SAT_, ModRef 2004.
 */
typedef struct Ladder Ladder;

/**
 * Implementations of the pairwise at-most-1 encoding.
 *
 * # References
 *
 * - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.
 */
typedef struct Pairwise Pairwise;

/**
 * Implementation of the binary adder tree totalizer encoding \[1\].
 * The implementation is incremental as extended in \[2\].
 * The implementation is based on a node database.
 * For now, this implementation only supports upper bounding.
 *
 * # References
 *
 * - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality
 *   Constraints_, CP 2003.
 * - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental
 *   Cardinality Constraints for MaxSAT_, CP 2014.
 */
typedef struct Totalizer Totalizer;

typedef void (*CClauseCollector)(int lit, void *data);

typedef void (*CAssumpCollector)(int lit, void *data);

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Creates a new [`Pairwise`] at-most-one encoding
 */
struct Pairwise *pairwise_new(void);

/**
 * Frees the memory associated with a [`Pairwise`]
 *
 * # Safety
 *
 * `pairwise` must be a return value of [`pairwise_new`] and cannot be used afterwards again.
 */
void pairwise_drop(struct Pairwise *pairwise);

/**
 * Adds a new input literal to a [`Pairwise`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `pairwise` must be a return value of [`pairwise_new`] that [`pairwise_drop`] has not yet been called on.
 */
enum MaybeError pairwise_add(struct Pairwise *pairwise,
                             int lit);

/**
 * Builds the [`Pairwise`] at-most-one encoding
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `pairwise` must be a return value of [`pairwise_new`] that [`pairwise_drop`] has not yet been called on.
 */
void pairwise_encode(struct Pairwise *pairwise,
                     uint32_t *n_vars_used,
                     CClauseCollector collector,
                     void *collector_data);

/**
 * Creates a new [`Ladder`] at-most-one encoding
 */
struct Ladder *ladder_new(void);

/**
 * Frees the memory associated with a [`Ladder`]
 *
 * # Safety
 *
 * `ladder` must be a return value of [`ladder_new`] and cannot be used afterwards again.
 */
void ladder_drop(struct Ladder *ladder);

/**
 * Adds a new input literal to a [`Ladder`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `ladder` must be a return value of [`ladder_new`] that [`ladder_drop`] has not yet been called on.
 */
enum MaybeError ladder_add(struct Ladder *ladder,
                           int lit);

/**
 * Builds the [`Ladder`] at-most-one encoding
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `ladder` must be a return value of [`ladder_new`] that [`ladder_drop`] has not yet been called on.
 */
void ladder_encode(struct Ladder *ladder,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Creates a new [`Bitwise`] at-most-one encoding
 */
struct Bitwise *bitwise_new(void);

/**
 * Frees the memory associated with a [`Bitwise`]
 *
 * # Safety
 *
 * `bitwise` must be a return value of [`bitwise_new`] and cannot be used afterwards again.
 */
void bitwise_drop(struct Bitwise *bitwise);

/**
 * Adds a new input literal to a [`Bitwise`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `bitwise` must be a return value of [`bitwise_new`] that [`bitwise_drop`] has not yet been called on.
 */
enum MaybeError bitwise_add(struct Bitwise *bitwise,
                            int lit);

/**
 * Builds the [`Bitwise`] at-most-one encoding
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `bitwise` must be a return value of [`bitwise_new`] that [`bitwise_drop`] has not yet been called on.
 */
void bitwise_encode(struct Bitwise *bitwise,
                    uint32_t *n_vars_used,
                    CClauseCollector collector,
                    void *collector_data);

/**
 * Creates a new [`Commander`] at-most-one encoding
 */
struct Commander *commander_new(void);

/**
 * Frees the memory associated with a [`Commander`]
 *
 * # Safety
 *
 * `commander` must be a return value of [`commander_new`] and cannot be used afterwards again.
 */
void commander_drop(struct Commander *commander);

/**
 * Adds a new input literal to a [`Commander`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `commander` must be a return value of [`commander_new`] that [`commander_drop`] has not yet been called on.
 */
enum MaybeError commander_add(struct Commander *commander,
                              int lit);

/**
 * Builds the [`Commander`] at-most-one encoding
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `commander` must be a return value of [`commander_new`] that [`commander_drop`] has not yet been called on.
 */
void commander_encode(struct Commander *commander,
                      uint32_t *n_vars_used,
                      CClauseCollector collector,
                      void *collector_data);

/**
 * Creates a new [`Bimander`] at-most-one encoding
 */
struct Bimander *bimander_new(void);

/**
 * Frees the memory associated with a [`Bimander`]
 *
 * # Safety
 *
 * `bimander` must be a return value of [`bimander_new`] and cannot be used afterwards again.
 */
void bimander_drop(struct Bimander *bimander);

/**
 * Adds a new input literal to a [`Bimander`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `bimander` must be a return value of [`bimander_new`] that [`bimander_drop`] has not yet been called on.
 */
enum MaybeError bimander_add(struct Bimander *bimander,
                             int lit);

/**
 * Builds the [`Bimander`] at-most-one encoding
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `bimander` must be a return value of [`bimander_new`] that [`bimander_drop`] has not yet been called on.
 */
void bimander_encode(struct Bimander *bimander,
                     uint32_t *n_vars_used,
                     CClauseCollector collector,
                     void *collector_data);

/**
 * Creates a new [`Totalizer`] cardinality encoding
 */
struct Totalizer *tot_new(void);

/**
 * Frees the memory associated with a [`Totalizer`]
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] and cannot be used afterwards again.
 */
void tot_drop(struct Totalizer *tot);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`tot_encode_ub`] following a call to this function are guaranteed to not increase
 * the value of `n_vars_used`. This does _not_ hold if [`tot_add`] is called in between
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
void tot_reserve(struct Totalizer *tot, uint32_t *n_vars_used);

/**
 * Adds a new input literal to a [`Totalizer`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
enum MaybeError tot_add(struct Totalizer *tot, int lit);

/**
 * Lazily builds the _change in_ cardinality encoding to enable upper bounds in a given range.
 * A change might be added literals or changed bounds.
 *
 * The min and max bounds are inclusive. After a call to [`tot_encode_ub`] with `min_bound=2` and
 * `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Panics
 *
 * If `min_bound > max_bound`.
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
void tot_encode_ub(struct Totalizer *tot,
                   size_t min_bound,
                   size_t max_bound,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns an assumption/unit for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`tot_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
enum MaybeError tot_enforce_ub(struct Totalizer *tot, size_t ub, int *assump);

/**
 * Lazily builds the _change in_ cardinality encoding to enable lower bounds in a given range.
 * A change might be added literals or changed bounds.
 *
 * The min and max bounds are inclusive. After a call to [`tot_encode_lb`] with `min_bound=2` and
 * `max_bound=4` bound including `>= 2` and `>= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Panics
 *
 * If `min_bound > max_bound`.
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
void tot_encode_lb(struct Totalizer *tot,
                   size_t min_bound,
                   size_t max_bound,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns an assumption/unit for enforcing a lower bound (`sum of lits >= lb`). Make sure that
 * [`tot_encode_lb`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
enum MaybeError tot_enforce_lb(struct Totalizer *tot, size_t lb, int *assump);

/**
 * Gets the next smaller upper bound value that can be encoded without setting tares. This is used
 * for coarse convergence.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
size_t dpw_coarse_ub(struct DynamicPolyWatchdog *dpw, size_t ub);

/**
 * Set the precision at which to build the encoding at. With `divisor = 8` the encoding will
 * effectively be built such that the weight of every input literal is divided by `divisor`
 * (integer division, rounding down). Divisor values must be powers of 2. After building the
 * encoding, the precision can only be increased, i.e., only call this function with _decreasing_
 * divisor values.
 *
 * # Errors
 *
 * - If `divisor` is not a power of 2, [`MaybeError::PrecisionNotPow2`] is returned
 * - If `divisor` is larger than the last divisor, i.e., precision is attempted to be decreased,
 *   [`MaybeError::PrecisionDecreased`] is returned
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
enum MaybeError dpw_set_precision(struct DynamicPolyWatchdog *dpw, size_t divisor);

/**
 * Gets the next possible precision divisor value
 *
 * Note that this is not the next possible precision value from the last _set_ precision but from
 * the last _encoded_ precision. The divisor value will always be a power of two so that calling
 * `set_precision` and then encoding will produce the smallest non-empty next segment of the
 * encoding.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
size_t dpw_next_precision(struct DynamicPolyWatchdog *dpw);

/**
 * Checks whether the encoding is already at the maximum precision
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
bool dpw_is_max_precision(struct DynamicPolyWatchdog *dpw);

/**
 * Given a range of output values to limit the encoding to, returns additional clauses that
 * "shrink" the encoding through hardening
 *
 * The output value range must be a range considering _all_ input literals, not only the encoded
 * ones.
 *
 * This is intended for, e.g., a MaxSAT solving application where a global lower bound is derived
 * and parts of the encoding can be hardened.
 *
 * The min and max bounds are inclusive. After a call to [`dpw_limit_range`] with `min_value=2`
 * and `max_value=4`, the encoding is valid for the value range `2 <= range <= 4`.
 *
 * To not specify a bound, pass `0` for the lower bound or `SIZE_MAX` for the upper bound.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 *
 * # Panics
 *
 * If `min_bound <= max_bound`.
 */
void dpw_limit_range(struct DynamicPolyWatchdog *dpw,
                     size_t min_value,
                     size_t max_value,
                     CClauseCollector collector,
                     void *collector_data);

/**
 * Creates a new [`GeneralizedTotalizer`] pseudo-Boolean encoding
 */
struct GeneralizedTotalizer *gte_new(void);

/**
 * Frees the memory associated with a [`GeneralizedTotalizer`]
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] and cannot be used afterwards again.
 */
void gte_drop(struct GeneralizedTotalizer *gte);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`gte_encode_ub`] following a call to this function are guaranteed to not increase
 * the value of `n_vars_used`. This does _not_ hold if [`gte_add`] is called in between
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 */
void gte_reserve(struct GeneralizedTotalizer *gte, uint32_t *n_vars_used);

/**
 * Adds a new input literal to a [`GeneralizedTotalizer`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 */
enum MaybeError gte_add(struct GeneralizedTotalizer *gte, int lit, size_t weight);

/**
 * Lazily builds the _change in_ pseudo-Boolean encoding to enable upper bounds in a given range.
 * A change might be added literals or changed bounds.
 *
 * The min and max bounds are inclusive. After a call to [`gte_encode_ub`] with `min_bound=2` and
 * `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Panics
 *
 * If `min_bound > max_bound`.
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 */
void gte_encode_ub(struct GeneralizedTotalizer *gte,
                   size_t min_bound,
                   size_t max_bound,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`gte_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`gte_enforce_ub`] returns.
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 */
enum MaybeError gte_enforce_ub(struct GeneralizedTotalizer *gte,
                               size_t ub,
                               CAssumpCollector collector,
                               void *collector_data);

/**
 * Creates a new [`BinaryAdder`] pseudo-Boolean encoding
 */
struct BinaryAdder *bin_adder_new(void);

/**
 * Frees the memory associated with a [`BinaryAdder`]
 *
 * # Safety
 *
 * `bin_adder` must be a return value of [`bin_adder_new`] and cannot be used afterwards again.
 */
void bin_adder_drop(struct BinaryAdder *bin_adder);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`bin_adder_encode_ub`] following a call to this function are guaranteed to not increase
 * the value of `n_vars_used`. This does _not_ hold if [`bin_adder_add`] is called in between
 *
 * # Safety
 *
 * `bin_adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been called on.
 */
void bin_adder_reserve(struct BinaryAdder *bin_adder,
                       uint32_t *n_vars_used);

/**
 * Adds a new input literal to a [`BinaryAdder`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `bin_adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been called on.
 */
enum MaybeError bin_adder_add(struct BinaryAdder *bin_adder,
                              int lit,
                              size_t weight);

/**
 * Lazily builds the _change in_ pseudo-Boolean encoding to enable upper bounds in a given range.
 * A change might be added literals or changed bounds.
 *
 * The min and max bounds are inclusive. After a call to [`bin_adder_encode_ub`] with `min_bound=2` and
 * `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Panics
 *
 * If `min_bound > max_bound`.
 *
 * # Safety
 *
 * `bin_adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been called on.
 */
void bin_adder_encode_ub(struct BinaryAdder *bin_adder,
                         size_t min_bound,
                         size_t max_bound,
                         uint32_t *n_vars_used,
                         CClauseCollector collector,
                         void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`bin_adder_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`bin_adder_enforce_ub`] returns.
 *
 * # Safety
 *
 * `bin_adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been called on.
 */
enum MaybeError bin_adder_enforce_ub(struct BinaryAdder *bin_adder,
                                     size_t ub,
                                     CAssumpCollector collector,
                                     void *collector_data);

/**
 * Lazily builds the _change in_ pseudo-Boolean encoding to enable lower bounds in a given range.
 * A change might be added literals or changed bounds.
 *
 * The min and max bounds are inclusive. After a call to [`bin_adder_encode_lb`] with `min_bound=2` and
 * `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Panics
 *
 * If `min_bound > max_bound`.
 *
 * # Safety
 *
 * `bin_adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been called on.
 */
void bin_adder_encode_lb(struct BinaryAdder *bin_adder,
                         size_t min_bound,
                         size_t max_bound,
                         uint32_t *n_vars_used,
                         CClauseCollector collector,
                         void *collector_data);

/**
 * Returns assumptions/units for enforcing a lower bound (`sum of lits <= ub`). Make sure that
 * [`bin_adder_encode_lb`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`bin_adder_enforce_ub`] returns.
 *
 * # Safety
 *
 * `bin_adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been called on.
 */
enum MaybeError bin_adder_enforce_lb(struct BinaryAdder *bin_adder,
                                     size_t lb,
                                     CAssumpCollector collector,
                                     void *collector_data);

/**
 * Creates a new [`DynamicPolyWatchdog`] pseudo-Boolean encoding
 */
struct DynamicPolyWatchdog *dpw_new(void);

/**
 * Frees the memory associated with a [`DynamicPolyWatchdog`]
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] and cannot be used afterwards again.
 */
void dpw_drop(struct DynamicPolyWatchdog *dpw);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`dpw_encode_ub`] following a call to this function are guaranteed to not increase
 * the value of `n_vars_used`. This does _not_ hold if [`dpw_add`] is called in between
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
void dpw_reserve(struct DynamicPolyWatchdog *dpw, uint32_t *n_vars_used);

/**
 * Adds a new input literal to a [`DynamicPolyWatchdog`] encoding
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *   [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
enum MaybeError dpw_add(struct DynamicPolyWatchdog *dpw, int lit, size_t weight);

/**
 * Lazily builds the _change in_ pseudo-Boolean encoding to enable upper bounds in a given range.
 * A change might be added literals or changed bounds.
 *
 * The min and max bounds are inclusive. After a call to [`dpw_encode_ub`] with `min_bound=2` and
 * `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Panics
 *
 * If `min_bound > max_bound`.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
void dpw_encode_ub(struct DynamicPolyWatchdog *dpw,
                   size_t min_bound,
                   size_t max_bound,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`dpw_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`dpw_enforce_ub`] returns.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
enum MaybeError dpw_enforce_ub(struct DynamicPolyWatchdog *dpw,
                               size_t ub,
                               CAssumpCollector collector,
                               void *collector_data);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#ifdef __cplusplus
}  // namespace RustSAT
#endif  // __cplusplus

#endif  /* rustsat_h */
