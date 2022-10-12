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
 * Low-Level C API for the MathSAT 5 solver
 *
 * Author: Alberto Griggio <griggio@fbk.eu>
 *
 * This file is part of MathSAT 5.
 */

#ifndef MSAT_MATHSATLL_H_INCLUDED
#define MSAT_MATHSATLL_H_INCLUDED

/**
 * \file mathsatll.h
 *
 * \brief Low-level API for the MathSAT SMT solver.
 */

#include "mathsat.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \brief Low-level inteface to the MathSAT DPLL(T) solver
 */
typedef struct msat_ll_solver { void *repr; } msat_ll_solver;

/**
 * \brief Low-level interface to SAT resultion proofs
 *
 * Note that these proofs do not contain any theory information. If you need
 * to access theory proofs, use the high-level interface
 * (see ::msat_get_proof_manager())
 */
typedef struct msat_satproof { void *repr; } msat_satproof;

/**
 * \brief SAT solver variables
 */
typedef int32_t msat_satvar;

/**
 * \brief SAT solver literals
 */
typedef int32_t msat_satlit;

/**
 * \brief special undefined SAT var
 */
#define msat_satvar_undef ((msat_satvar)0)

/**
 * \brief special undefined SAT lit
 */
#define msat_satlit_undef ((msat_satlit)0)

/**
 * \brief literal creation from a variable and a sign
 */
#define msat_make_satlit(var, neg) ((neg) ? -(var) : (var))

/**
 * \brief get the variable corresponding to \a lit
 */
#define msat_satlit_var(lit) ((lit) < 0 ? -(lit) : (lit))

/**
 * \brief check whether the literal is negated
 */
#define msat_satlit_negated(lit) ((lit) < 0)

/**
 * \brief negate a literal
 */
#define msat_satlit_negate(lit) (-(lit))

/**
 * \brief Error checking for ::msat_ll_solver
 */
#define MSAT_ERROR_LL_SOLVER(s) ((s).repr == NULL)

/**
 * \brief Error checking for ::msat_satproof
 */
#define MSAT_ERROR_SATPROOF(s) ((s).repr == NULL)

/**
 * \brief Create a low-level DPLL(T) solver
 *
 * Configuration parameters are read from the parent environment 
 *
 * \param env The parent environment
 * \param tsolver If nonzero, enable support for theories,
 *        otherwise a pure SAT solver is created
 *
 * \return the created SAT solver. In case of errors, a solver s.t.
 *         MSAT_ERROR_SATSOLVER(solver) is true is returned
 */
msat_ll_solver msat_create_ll_solver(msat_env env, int tsolver);

/**
 * \brief Destroys a low-level DPLL(T) solver
 *
 * \param s The solver to destroy
 * \return zero on success, nonzero on error
 */
int msat_destroy_ll_solver(msat_ll_solver s);

/**
 * \brief Create a new variable in the SAT solver
 *
 * \param s The solver in which to operate
 * \return The new variable, or msat_satvar_undef on error
 */
msat_satvar msat_ll_make_var(msat_ll_solver s);

/**
 * \brief Create a proxy variable for the given theory atom
 *
 * Note that this does *not* add constraints for encoding unsupported
 * functions/predicates automatically. In order to ensure correctness, you
 * must manually call ::msat_ll_encode_constraints()
 *
 * \param s The solver in which to operate
 * \param atom The atom to proxy
 * \return A proxy variable for \a atom, or msat_satvar_undef on error
 */
msat_satvar msat_ll_make_proxy_var(msat_ll_solver s, msat_term atom);

/**
 * \brief sets the polarity used when branching on the variable \a v
 *
 * If pol is MSAT_UNDEF, the default polarity will be used
 *
 * \param s The solver in which to operate
 * \param v The variable to set the polarity
 * \param pol The polarity value
 *
 * \return zero on success, nonzero on error
 *
 */ 
int msat_ll_set_var_polarity(msat_ll_solver s, msat_satvar v,
                             msat_truth_value pol);

/**
 * \brief Enable/disable branching on \a v
 *
 * \param s The solver in which to operate
 * \param v The variable to set the branching
 * \param yes If nonzero, enable branching on this variable
 *
 * \return zero on success, nonzero on error
 */ 
int msat_ll_set_var_decision(msat_ll_solver s, msat_satvar v, int yes);

/**
 * \brief Adds a variable at the end of the list of preferred
 *        variables for branching when solving the problem
 *
 * The polarity can be controlled with ::msat_ll_set_var_polarity()
 *        
 * \param s The solver in which to operate
 * \param v The variable to add to the preferred list
 * \return zero on success, nonzero on error
 */
int msat_ll_add_preferred_var(msat_ll_solver s, msat_satvar v);

/**
 * \brief Clears the list of preferred variables for branching
 *
 * \param s The solver in which to operate
 * \return zero on success, nonzero on error
 */
int msat_ll_clear_preferred_vars(msat_ll_solver s);

/**
 * \brief Generate a list of additional axioms encoding unsupported
 *        functions/predicates in \a term.
 *
 * Each term in the returned array is an additional axiom that should be added
 * to \a s. Note that axioms can be arbitrary formulas, and so must be
 * converted to CNF to be added to the solver.
 *
 * Calling this function is necessary for correctness whenever \a term
 * contains subterms with the following tags:
 * 
 * - MSAT_TAG_TERM_ITE
 * 
 * - MSAT_TAG_INT_MOD_CONGR
 * 
 * - MSAT_TAG_FLOOR
 * 
 * - MSAT_TAG_INT_TO_BV
 * 
 * - MSAT_TAG_INT_FROM_UBV
 * 
 * - MSAT_TAG_INT_FROM_SBV
 *
 * \param s The solver in which to operate
 * \param term The term containing the constraints to encode
 * \param out_n Output parameter for storing the size of the returned array.
 *              Must not be NULL
 *              
 * \return an array of additional axioms to add to the solver, or NULL in case
 *         of error. The array must be deallocated by the user with
 *         ::msat_free()
 */
msat_term *msat_ll_encode_constraints(msat_ll_solver s, msat_term term,
                                      size_t *out_n);

/**
 * \brief starts a new clause in the solver
 *
 * \param s The solver in which to operate
 * \return zero on success, nonzero on error
 */
int msat_ll_begin_clause(msat_ll_solver s);

/**
 * \brief adds a literal to the current clause in the solver
 *
 * \param s The solver in which to operate
 * \param l The literal to add
 * \return zero on success, nonzero on error
 */
int msat_ll_addlit(msat_ll_solver s, msat_satlit l);

/**
 * \brief Ends the current clause in the solver
 *
 * \param s The solver in which to operate
 * \return zero on success, nonzero on error
 */
int msat_ll_end_clause(msat_ll_solver s);

/**
 * \brief Pushes a checkpoint for backtracking in the solver
 *
 * \param s The solver in which to operate
 * \return zero on success, nonzero on error
 */
int msat_ll_push_backtrack_point(msat_ll_solver s);

/**
 * \brief Backtracks to the last checkpoint set in the solver
 *
 * \param s The solver in which to operate
 * \return zero on success, nonzero on error
 */
int msat_ll_pop_backtrack_point(msat_ll_solver s);

/**
 * \brief Checks satisfiability under the given assumptions
 *
 * \param s The solver in which to operate
 * \param assumptions An optional list of assumption literals (can be  NULL)
 * \param num_assumptions The size of the \a assumption array
 * 
 * \return ::MSAT_SAT if the problem is satisfiable, ::MSAT_UNSAT if it is
 *         unsatisfiable, and ::MSAT_UNKNOWN if there was some error or if
 *         the satisfiability can't be determined.
 */
msat_result msat_ll_solve(msat_ll_solver s, msat_satlit *assumptions,
                          size_t num_assumptions);

/**
 * \brief Returns a string with search statistics for the given solver
 *
 * The returned string will contain newline-separated statistics for the DPLL
 * engine and the active theory solvers (if any).
 *
 * \param s The solver in which to operate.
 * \return A string with search statistics, or NULL in case of errors.
 *         The string must be deallocated by the oser with ::msat_free(). 
 */
char *msat_ll_get_search_stats(msat_ll_solver s);

/**
 * \brief Tests whether the given assumption is part of the unsatisfiable core
 * 
 * \param s The solver in which to operate
 * \param l The assumption to test
 * \return 1 if \a l is in the unsat core, 0 if not, -1 on error
 */
int msat_ll_is_unsat_assumption(msat_ll_solver s, msat_satlit l);

/**
 * \brief Retrieves the truth assignment for the given variable in the solver
 *
 * \param s The solver in which to operate
 * \param v A variable
 * \return The truth assignment for \a v in \a s, or MSAT_UNDEF in case of
 *         errors (or if the value is actually unknown)
 */
msat_truth_value msat_ll_get_model_value(msat_ll_solver s, msat_satvar v);

/**
 * \brief Asks the solver to construct a theory model
 *
 * \param s The solver in which to operate
 * \return zero on success, nonzero on error
 */
int msat_ll_build_theory_model(msat_ll_solver s);

/**
 * \brief Retrieves the model value for the given term
 *
 * Model generation must be enabled in the environment passed to
 * ::msat_create_ll_solver(). Before invoking this function, you must call
 * ::msat_ll_build_theory_model()
 *
 * \param s The solver in which to operate
 * \param v A term
 * \return The model value for \a v in \a s, or a t s.t.
 *         MSAT_ERROR_TERM(t) is true in case of errors
 */
msat_term msat_ll_get_theory_model_value(msat_ll_solver s, msat_term v);

/**
 * \brief Retrieves the resolution proof of unsatisfiability computed by the
 *        solver
 *
 * Proof generation must be enabled in the environment passed to
 * ::msat_create_ll_solver()
 *
 * \param s The solver in which to operate
 * \return the resolution refutation, or a proof p s.t. MSAT_ERROR_SATPROOF(p)
 *         is true in case of errors
 */
msat_satproof msat_ll_get_unsat_proof(msat_ll_solver s);

/**
 * \brief Checks whether the given proof is a resolution chain
 *
 * \param p A resolution proof
 * \return 1 of the proof is a resolution chain, 0 if not, -1 on error
 */
int msat_satproof_is_res(msat_satproof p);

/**
 * \brief Returns the arity of the given resolution chain
 *
 * \param p A resolution chain
 * \return the arity of \a p, or -1 on error
 */
int msat_satproof_res_arity(msat_satproof p);

/**
 * \brief Retrieves the step at index \a idx of the given resolution chain
 *
 * A step consists of a pair (pivot_literal, right_branch), where the left
 * branch is the current proof \a p.
 *
 * \param p A resolution chain
 * \param idx The index of the step to retrieve
 * \param pivot Output parameter for the pivot. If \a idx is zero,
 *              the pivot is msat_satlit_undef
 * \param c Output parameter for the right branch of the resolution
 *
 * \return zero on success, nonzero on error
 */
int msat_satproof_res_step(msat_satproof p, int idx,
                           msat_satlit *pivot, msat_satproof *c);

/**
 * \brief Retrieves the arity of the clause attached to the given leaf proof
 *
 * \param p A leaf proof
 * \return the clause arity, or -1 on error
 */
int msat_satproof_clause_arity(msat_satproof p);

/**
 * \brief Retrieves the literal at the given index in the clause attached to
 * the given leaf proof
 *
 * \param p A leaf proof
 * \param idx The index of the literal to retrieve
 * \return the literal at the given index, or msat_satlit_undef on error
 */
msat_satlit msat_satproof_clause_lit(msat_satproof p, int idx);

#ifdef __cplusplus
} /* end of extern "C" */
#endif

#endif /* MSAT_MATHSATLL_H_INCLUDED */
