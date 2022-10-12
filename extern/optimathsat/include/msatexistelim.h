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
 * Existential quantifier elimination API for the MathSAT SMT solver
 *
 * Author: Alberto Griggio <griggio@fbk.eu>
 *
 * This file is part of MathSAT 5.
 */

/**
 * \file msatexistelim.h
 *
 * \brief Existential quantifier elimination API for the MathSAT SMT solver.
 */

#ifndef MSAT_MSATEXISTELIM_H_INCLUDED
#define MSAT_MSATEXISTELIM_H_INCLUDED

#include "mathsat.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
    MSAT_EXIST_ELIM_ALLSMT_FM,  /**< All-SMT and Fourier-Motzkin projection */
    MSAT_EXIST_ELIM_VTS         /**< Virtual term substitutions */
} msat_exist_elim_algorithm;

#define MSAT_EXIST_ELIM_LW MSAT_EXIST_ELIM_VTS /** backwards compatibility */

typedef struct {
    int toplevel_propagation; /**< enable toplevel propagation */
    int boolean_simplifications; /**< enable simplifications to the Boolean
                                  **< structure of the formula using
                                  **< And-Inverter Graph rewriting */
    int remove_redundant_constraints; /**< enable aggressive simplifications
                                       **< of redundant linear inequalities
                                       **< (can be very expensive) */
} msat_exist_elim_options;

/**
 * Performs existential quantifier elimination from an arbitrary formula
 *
 * Note: it does not do advanced simplifications like pushing quantifiers
 */
msat_term msat_exist_elim(msat_env env, msat_term formula,
                          msat_term *vars_to_elim, size_t num_vars_to_elim,
                          msat_exist_elim_algorithm algo,
                          msat_exist_elim_options options);

/**
 * Model-based existential quantifier elimination, using virtual term
 * substitutions
 *
 * \param env The environment in which to operate
 * \param formula The target formula
 * \param vars_to_elim Array of variables to eliminate
 * \param num_vars_to_elim Size of \a vars_to_elim
 * \param model_vars Variables in the model
 * \param model_values Values for variables in the model
 * \param model_size Size of the model
 *
 * \return the model-based elimination of \a formula, or a term t
 * s.t. MSAT_ERROR_TERM(t) is true in case of errors
 */
msat_term msat_exist_elim_model(msat_env env, msat_term formula,
                                msat_term *vars_to_elim,
                                size_t num_vars_to_elim,
                                msat_term *model_vars,
                                msat_term *model_values,
                                size_t model_size);

/**
 * Simplifies the Boolean structure of an arbitrary formula using AIGs with
 * local two-level rewriting
 */
msat_term msat_aig_simplify(msat_env env, msat_term formula);


/**
 * Puts the input formula in negation normal form
 */
msat_term msat_to_nnf(msat_env env, msat_term formula);

/**
 * LRA-specific simplification of the formula
 */
msat_term msat_lra_simplify(msat_env env, msat_term formula);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* MSAT_MSATEXISTELIM_H_INCLUDED */
