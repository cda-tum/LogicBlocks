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
 * AIG C API for the MathSAT 5 solver
 *
 * Author: Alberto Griggio <griggio@fbk.eu>
 *
 * This file is part of MathSAT 5.
 */

#ifndef MSAT_MATHSATAIG_H_INCLUDED
#define MSAT_MATHSATAIG_H_INCLUDED

/**
 * \file mathsataig.h
 *
 * \brief AIG (And-inverter graphs) API for the MathSAT SMT solver.
 */

#include "mathsat.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uintptr_t msat_aig;

typedef struct msat_aig_manager { void *repr; } msat_aig_manager;

msat_aig_manager msat_create_aig_manager(msat_env env);
int MSAT_ERROR_AIG_MANAGER(msat_aig_manager mgr);
void msat_destroy_aig_manager(msat_aig_manager mgr);

msat_aig msat_aig_true(msat_aig_manager mgr);
msat_aig msat_aig_false(msat_aig_manager mgr);
msat_aig msat_aig_var(msat_aig_manager mgr, int v);
msat_aig msat_aig_and(msat_aig_manager mgr, msat_aig a1, msat_aig a2);
msat_aig msat_aig_not(msat_aig a);
msat_aig msat_aig_or(msat_aig_manager mgr, msat_aig a, msat_aig b);
msat_aig msat_aig_ite(msat_aig_manager mgr, msat_aig c, msat_aig t, msat_aig e);
msat_aig msat_aig_iff(msat_aig_manager mgr, msat_aig a, msat_aig b);
msat_aig msat_aig_xor(msat_aig_manager mgr, msat_aig a, msat_aig b);
msat_aig msat_aig_null(void);
size_t msat_aig_id(msat_aig a);
int msat_aig_is_negated(msat_aig a);
int msat_aig_is_and(msat_aig a);
int msat_aig_get_var(msat_aig a);
msat_aig msat_aig_get_left(msat_aig a);
msat_aig msat_aig_get_right(msat_aig a);
msat_aig msat_aig_strip(msat_aig a);

char *msat_aig_to_aiger(msat_aig_manager mgr, msat_aig a);

msat_aig *msat_aig_encode(msat_aig_manager mgr, msat_term t, size_t *out_size);

#ifdef __cplusplus
} /* end of extern "C" */
#endif

#endif /* MSAT_MATHSATAIG_H_INCLUDED */
