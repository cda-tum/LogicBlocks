/* -*- C -*-
 *
 * MathSAT5 is copyrighted 2009-2021 by Fondazione Bruno Kessler, Trento, Italy,
 * University of Trento, Italy, and others. All rights reserved.
 * 
 * MathSAT5 is available for research and evaluation purposes only.
 * It can not be used in a commercial environment, particularly as part of a
 * commercial product, without written permission. MathSAT5 is provided as is,
 * without any warranty.
 * 
 * Please write to mathsat@fbk.eu for additional questions regarding licensing
 * MathSAT5 or obtaining more up-to-date versions.
 *
 * C API for the OptiMathSAT solver
 *
 * Author: Patrick Trentin <patrick.trentin@unitn.it>
 *
 * This file is part of OptiMathSAT.
 */

/**
 * \file optimathsat.h
 *
 * \brief API for the OptiMathSAT OMT solver.
 */

#ifndef MSAT_OPTIMATHSAT_H_INCLUDED
#define MSAT_OPTIMATHSAT_H_INCLUDED

#include "mathsat.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \brief OptiMathSAT objective.
 *
 * An objective is a term which is optimized upon solve calls.
 */
typedef struct msat_objective { void *repr; } msat_objective;

/**
 * \brief Pareto Model handler.
 *
 * A handler for the model found in pareto optimization when
 * the solver is executed in callback mode.
 */
typedef struct msat_pareto_model_handler { void *repr; } msat_pareto_model_handler;

/**
 * \brief External MaxSAT Engine.
 *
 * The external MaxSAT engine to be used for MaxSMT optimization
 */
typedef struct msat_ext_maxsat { void *repr; } msat_ext_maxsat;

/**
 * \brief Interface that external MaxSAT solvers must implement.
 */
typedef struct msat_ext_maxsat_interface {
    /*
     * Adds a soft clause, i.e. a clause which does not have to be satisfied,
     * but falsifying incurs cost weight
     */
    void (*add_soft_clause)(void *self, int* clause, long weight);

    /*
     * Adds a hard clause, i.e. a clause which must be satisfied
     */
    void (*add_hard_clause)(void *self, int*  clause, int permanent);

    /*
     * Decides the minimum cost at which the current formula can be solved,
     * -1 means no solution exists.
     */
    long (*solve)(void *self);

    /*
     * If it is decided that the current formula can be solved, this method
     * returns the model value of var.
     */
    int (*get_model_value)(void *self, int var);

} msat_ext_maxsat_interface;

/**
 * OptiMathSAT codes for queries on objective items
 */
typedef enum {
    MSAT_OPTIMUM = 0,
    MSAT_FINAL_LOWER = 1,
    MSAT_FINAL_UPPER = 2,
    MSAT_FINAL_ERROR = 3,
} msat_objective_value;

/**
 * OptiMathSAT objective type, either minimize or maximize
 */
typedef enum {
    MSAT_OBJECTIVE_MINIMIZE = -1,  /* objective should be minimized */
    MSAT_OBJECTIVE_UNKNOWN  = 0,   /* unknown/error objective       */
    MSAT_OBJECTIVE_MAXIMIZE =  1   /* objective should be maximized */
} msat_objective_type;

/**
 * OptiMathSAT objective search status
 */
typedef enum {
    MSAT_OPT_UNKNOWN = -1,
    MSAT_OPT_UNSAT   = 0,
    MSAT_OPT_SAT_PARTIAL = 1,        /* objective partially optimized, solution available */
    MSAT_OPT_SAT_APPROX  = 2,        /* objective solution approximates optimal one */
    MSAT_OPT_SAT_OPTIMAL = 3         /* objective solution certified to be optimal */
} msat_opt_result;

/**
 * Opt Priority
 */
typedef enum {
    MSAT_OPT_BOX = 0,
    MSAT_OPT_LEX = 1,
    MSAT_OPT_PAR = 2
} msat_opt_priority;

/**
 * \brief MathSAT objective stack iterator.
 *
 * An iterator object that lets you retrieve the state of optimized objectives
 * and their associated model.
 */
typedef struct msat_objective_iterator { void *repr; } msat_objective_iterator;

/**
 * \brief Callback function to be notified about models found during
 *        optimization, e.g. by Pareto algorithm or sub-optimal models
 *
 * This callback function can be used to be notified about the models found by
 * the Pareto Optimization search. If the function returns zero, then the
 * current search is aborted
 */
typedef int (*msat_opt_model_callback)(msat_objective_iterator it,
                                       msat_model_iterator jt,
                                       void *user_data);

/**
 * \name OptiMathSAT - Optimizing Environment
 */
/*@{*/

/**
 * \brief Creates a new OptiMathSAT environment from the given configuration
 * \param cfg The configuration to use
 * \return A new environment. Use ::MSAT_ERROR_ENV to check for errors
 */
msat_env msat_create_opt_env(msat_config cfg);

/**
 * \brief Creates an environment that can share terms with its \a sibling
 * \param cfg The configuration to use.
 * \param sibling The environment with which to share terms
 * \return A new environment. Use ::MSAT_ERROR_ENV to check for errors
 *
 * Note: attempting the instance of shared environment must be destroyed
 *       before the one it originates from. Otherwise, the behaviour is
 *       undefined.
 */
msat_env msat_create_shared_opt_env(msat_config cfg, msat_env sibling);

/*@}*/ /* end of Optimizing Environment group */

/**
 * \name OptiMathSAT - objectives
 */
/*@{*/

/**
 * \brief Creates a new objective 'min(term)'
 *
 * \param e The environment in which to operate.
 * \param term  The term to be minimized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_minimize(msat_env e, msat_term term);

/**
 * \brief Creates a new objective 'min(term)'
 *
 * If term is a bitvector, it is interpreted as signed.
 *
 * \param e The environment in which to operate.
 * \param term  The term to be minimized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_minimize_signed(msat_env e, msat_term term);

/**
 * \brief Creates a new objective 'max(term)'
 *
 * \param e The environment in which to operate.
 * \param term  The term to be maximized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_maximize(msat_env e, msat_term term);

/**
 * \brief Creates a new objective 'max(term)'
 *
 * If term is a bitvector, it is interpreted as signed.
 *
 * \param e The environment in which to operate.
 * \param term  The term to be maximized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_maximize_signed(msat_env e, msat_term term);

/**
 * \brief Creates a new objective 'min(max(term0), ..., max(termN))'
 *
 * \param e The environment in which to operate.
 * \param len The size of terms.
 * \param terms The array of terms to be optimized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_minmax(msat_env e, size_t len, msat_term *terms);

/**
 * \brief Creates a new objective 'min(max(term0), ..., max(termN))'
 *
 * If terms are bitvectors, they are interpreted as signed.
 *
 * \param e The environment in which to operate.
 * \param len The size of terms.
 * \param terms The array of terms to be optimized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_minmax_signed(msat_env e, size_t len, msat_term *terms);

/**
 * \brief Creates a new objective 'max(min(term0), ..., min(termN))'
 *
 * \param e The environment in which to operate.
 * \param len The size of terms.
 * \param terms The array of terms to be optimized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_maxmin(msat_env e, size_t len, msat_term *terms);

/**
 * \brief Creates a new objective 'max(min(term0), ..., min(termN))'
 *
 * If terms are bitvectors, they are interpreted as signed.
 *
 * \param e The environment in which to operate.
 * \param len The size of terms.
 * \param terms The array of terms to be optimized.
 *
 * \return An objective, or a o s.t. ::MSAT_ERROR_OBJECTIVE(o) is true
 * in case of errors.
 */
msat_objective msat_make_maxmin_signed(msat_env e, size_t len, msat_term *terms);

/**
 * \brief Push a msat_objective on the objective stack
 * \param e The Environment in which the objective is pushed
 * \param o The msat_objective to push
 *
 * \return zero on success, nonzero on error.
 */
int msat_assert_objective(msat_env e, msat_objective o);

/**
 * \brief Destroys a msat_objective
 * \param e The Environment in which the objective was created
 * \param o The msat_objective to destroy
 */
void msat_destroy_objective(msat_env e, msat_objective o);

/**
 * \brief Associate a weight to a term declaration with respect to a MaxSMT
 * group identified by a common id label. Assert-soft constraints are ineffective
 * unless the id label is used by an objective that is pushed on the stack
 *
 * \param e The environment in which to operate.
 * \param term The term to which a weight is attached.
 * \param weight The weight of not satisfying this soft-clause.
 * \param id The MaxSMT sum onto which the weight contribution is added.
 *
 * \return zero on success, nonzero on error.
 */
int msat_assert_soft_formula(msat_env e, msat_term term, msat_term weight,
                             const char *id);

/*@}*/ /* end of objectives group */


/**
 * \name OptiMathSAT - pareto optimization support
 */
/*@{*/

/**
 * \brief Creates a custom Pareto Optimization Callback Function
 *
 * \param func The user-defined call-back function to print Pareto models.
 * \param user_data Generic data pointer which will be passed to \a func. Can
 *                  be anything, its value will not be interpreted.
 * \return A pointer to an instance of \a msat_pareto_model_handler, which
 *         must be destroyed with msat_destroy_pareto_model_handler()
 */
msat_pareto_model_handler msat_create_pareto_model_handler(
        msat_opt_model_callback func,
        void *user_data);

/**
 * \brief Installs a custom Pareto Optimization Callback Function
 *        in the given environment.
 *
 * The \a func function is invoked each time a new model is found by
 * the pareto optimization search. If the function returns zero, then
 * the current search is aborted.
 *
 * The Pareto Optimization Callback Function is only necessary if
 * option 'opt.par.mode' is equal to 'CALLBACK'. Otherwise, Pareto
 * search is done incrementally through a sequence of check-sat calls.
 *
 * \param env The environment in which to operate.
 * \param func The user-defined call-back function to print Pareto models.
 *             If it is NULL, attempting to perform a pareto-optimization
 *             search yields an error.
 * \param user_data Generic data pointer which will be passed to \a func. Can
 *                  be anything, its value will not be interpreted.
 * \return zero on success, nonzero on error
 */
int msat_set_pareto_model_handler(msat_env env,
                                  msat_pareto_model_handler func);

/**
 * \brief Uninstalls a custom Pareto Optimization Callback Function
 *        from the given environment.
 *
 * \param env The environment in which to operate.
 * \return zero on success, nonzero on error
 */
int msat_unset_pareto_model_handler(msat_env env);

/**
 * \brief Destroy a custom Pareto Optimization Callback Function
 *
 * \param func The user-defined call-back function to print Pareto models.
 */
void msat_destroy_pareto_model_handler(msat_pareto_model_handler func);

/**
 * \brief Sets the multi-objective optimization priority to
 * one of the supported algorithms.
 *
 * \param e The environment in which to operate
 * \param p The optimization algorithm to use
 * \return zero on success, nonzero on error
 */
int msat_set_opt_priority(msat_env e, msat_opt_priority p);

/*@}*/ /* end of pareto optimization group */

/**
 * \name External MaxSAT - Lemma Lifting
 */
/*@{*/

/**
 * \brief Creates an external maxsat engine reference
 *
 * \param im The user-defined external maxsat interface
 * \return A pointer to an instance of \a msat_ext_maxsat, which
 *         must be destroyed with msat_destroy_ext_maxsat_engine()
 */
msat_ext_maxsat msat_create_ext_maxsat_engine(msat_ext_maxsat_interface *im);

/**
 * \brief Sets an external MaxSAT engine to be used by an Environment
 *
 * \param env The environment in which to operate.
 * \param em  The external maxsat engine to use.
 * \return zero on success, nonzero on error
 */
int msat_set_ext_maxsat_engine(msat_env env,
                               msat_ext_maxsat em);

/**
 * \brief Unsets the external MaxSAT engine from the given Environment
 *
 * \param env The environment in which to operate.
 * \return zero on success, nonzero on error
 */
int msat_unset_ext_maxsat_engine(msat_env env);

/**
 * \brief Destroys an external MaxSAT engine reference
 *
 * \param em The external maxsat engine reference.
 */
void msat_destroy_ext_maxsat_engine(msat_ext_maxsat em);

/*@}*/ /* end of external MaxSAT - Lemma Lifting group */

/**
 * \name OptiMathSAT - objective stack iterator
 */
/*@{*/

/**
 * \brief Creates an objective iterator
 *
 * NOTE: an objective iterator, and any of its references, should only be
 * instantiated after a ::msat_solve call, and prior to any further
 * push/pop/assert_objective/assert_soft_formula/assert_formula action.
 * Otherwise, the behaviour is undefined.
 *
 * \param e The environment in use
 * \return an iterator for the current objectives
 */
msat_objective_iterator msat_create_objective_iterator(msat_env e);

/**
 * \brief Checks whether \a i can be incremented
 * \param i An objective iterator
 * \return nonzero if \a i can be incremented, zero otherwise
 */
int msat_objective_iterator_has_next(msat_objective_iterator i);

/**
 * \brief Returns the next objective, and increments the given iterator
 * \param i The objective iterator to increment.
 * \param o Output value for the next objective in the stack.
 * \return nonzero in case of error.
 */
int msat_objective_iterator_next(msat_objective_iterator i, msat_objective *o);

/**
 * \brief Destroys an objective iterator.
 * \param i the iterator to destroy.
 */
void msat_destroy_objective_iterator(msat_objective_iterator i);

/*@}*/ /* end of objective stack iterator group */

/**
 * \name OptiMathSAT - functions for objective state inspection
 */
/*@{*/

/**
 * \brief Returns the optimization search state of the given objective
 * \param e The environment in which to operate.
 * \param o The objective.
 * \return
 * - ::MSAT_OPT_UNKNOWN if there was some error or if satisfiability/
 *   unsatisfiability could not be determined
 * - ::MSAT_OPT_UNSAT if objective is unsatisfiable
 * - ::MSAT_OPT_SAT_PARTIAL if optimization search found some solution, but
 *   it is not certified to be optimal
 * - ::MSAT_OPT_SAT_APPROX if optimization search found some solution and
 *   that solution meets early termination criteria
 * - ::MSAT_OPT_SAT_OPTIMAL if optimization search found a certified
 *   optimal solution
 */
msat_opt_result msat_objective_result(msat_env e, msat_objective o);

/**
 * \brief Returns the term which is optimized by the objective
 * \param e The environment in which to operate.
 * \param o The objective.
 * \return msat_term representation of the objective function
 */
msat_term msat_objective_get_term(msat_env e, msat_objective o);

/**
 * \brief Returns the objective optimization type (min or max)
 * \param e The environment in which to operate.
 * \param o The objective.
 * \returns ::MSAT_OBJECTIVE_MINIMIZE or ::MSAT_OBJECTIVE_MAXIMIZE
 */
msat_objective_type msat_objective_get_type(msat_env e, msat_objective o);

/**
 * \brief Load into memory the model associated with the given objective,
 * provided that it is satisfiable.
 * \param e The environment in which to operate.
 * \param o The objective providing the model.
 * \return zero on success, nonzero on error.
 */
int msat_load_objective_model(msat_env e, msat_objective o);

/**
 * \brief Returns optimization search statistics.
 * \return A string which provides some search statistics information
 *         on the optimization search of the given objective.
 *         The string must be deallocated by the user with ::msat_free().
 */
char* msat_objective_get_search_stats(msat_env e, msat_objective o);

/**
 * \brief Determines if the given objective value is unbounded.
 * \param e The environment in which to operate.
 * \param o The objective providing the value.
 * \param i The objective field to be tested.
 * \return 1 if unbounded, 0 if not, -1 on error.
 */
int msat_objective_value_is_unbounded(msat_env e, msat_objective o, msat_objective_value i);

/**
 * \brief Determines if the given objective value is +INF.
 * \param e The environment in which to operate.
 * \param o The objective providing the value.
 * \param i The objective field to be tested.
 * \return 1 if +INF, 0 if not, -1 on error.
 */
int msat_objective_value_is_plus_inf(msat_env e, msat_objective o, msat_objective_value i);

/**
 * \brief Determines if the given objective value is -INF.
 * \param e The environment in which to operate.
 * \param o The objective providing the value.
 * \param i The objective field to be tested.
 * \return 1 if -INF, 0 if not, -1 on error.
 */
int msat_objective_value_is_minus_inf(msat_env e, msat_objective o, msat_objective_value i);

/**
 * \brief Determines if the given objective value is strict,
 *    (e.g. if term(i) = k and strict(i) = TRUE, then actual value of 'i' is k+epsilon,
 *    with epsilon being any small positive value)
 * \param e The environment in which to operate.
 * \param o The objective providing the value.
 * \param i The objective field to be tested.
 * \return 1 if strict, 0 if not, -1 on error.
 */
int msat_objective_value_is_strict(msat_env e, msat_objective o,
                                   msat_objective_value i);

/**
 * \brief Returns the value of epsilon of a strict
 *        objective value.
 * \param e The environment in which to operate.
 * \param o The objective providing the value.
 * \param i The objective field to be tested.
 * \return  1 if the objective value is equal to k + epsilon
 *          0 if the objective value is equal to k
 *         -1 if the objective value is equal to k - epsilon
 *         where epsilon is a a symbolic, arbitrary small, value.
 */
int msat_objective_value_get_epsilon(msat_env e, msat_objective o,
                                     msat_objective_value i);

/**
 * \brief Returns term representation of the given objective value.
 *        A suitable representation is chosen by the OMT solver for
 *        any value which cannot be directly represented in the LA-Theory
 *        (e.g. -oo/+oo and K + epsilon) using either the arguments
 *        inf/eps or, if not valid, some internal heuristics.
 *
 * \param e The environment in which to operate.
 * \param o The objective providing the value.
 * \param i The objective field to retrieve.
 * \param inf The symbol / positive value representation for infinity
 * \param eps The symbol / positive value representation for epsilon
 * \return term associated to the objective value, or msat_error_term on error.
 */
msat_term msat_objective_value_term(msat_env e, msat_objective o,
                                    msat_objective_value i,
                                    msat_term inf, msat_term eps);

/**
 * \brief Returns model associated with the given objective, if any
 * \param e The environment in which to operate.
 * \param o The objective which has been optimized
 * \return A model object. Use MSAT_ERROR_MODEL to check for errors.
 *         The model object should be deallocated with ::msat_destroy_model
 */
msat_model msat_objective_get_model(msat_env e, msat_objective o);

/*@}*/ /* end of functions for objective state inspection group */

#ifdef __cplusplus
} /* end of extern "C" */
#endif

#endif /* MSAT_OPTIMATHSAT_H_INCLUDED */

