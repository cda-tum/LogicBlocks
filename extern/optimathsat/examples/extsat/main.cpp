#include "mathsat.h"
#include "msatminisat.h"
#include "msatcleaneling.h"
#include <stdio.h>
#include <string.h>

typedef enum {
    DPLL_MINISAT,
    DPLL_CLEANELING,
    DPLL_ERROR
} dpll_engine;


dpll_engine get_engine(int argc, const char **argv)
{
    if (argc != 2) {
        return DPLL_ERROR;
    }
    if (strcmp(argv[1], "minisat") == 0) {
        return DPLL_MINISAT;
    } else if (strcmp(argv[1], "cleaneling") == 0) {
        return DPLL_CLEANELING;
    }
    return DPLL_ERROR;
}

int main(int argc, const char **argv)
{
    dpll_engine e = get_engine(argc, argv);
    if (e == DPLL_ERROR) {
        printf("Usage: %s [minisat|cleaneling] < benchmark.smt2\n", argv[0]);
        return 1;
    }
    
    msat_config cfg = msat_create_config();
    msat_env env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    minisat_dpll_engine me;
    cleaneling_dpll_engine ce;

    if (e == DPLL_MINISAT) {
        init_minisat_solver(&me);
        msat_set_external_dpll_engine(env, (msat_ext_dpll_interface *)(&me));
    } else {
        init_cleaneling_solver(&ce);
        msat_set_external_dpll_engine(env, (msat_ext_dpll_interface *)(&ce));
    }

    msat_term formula = msat_from_smtlib2_file(env, stdin);
    msat_assert_formula(env, formula);

    msat_result status = msat_solve(env);

    char *stats = msat_get_search_stats(env);
    puts("\nMathSAT statistics:\n");
    puts(stats);
    msat_free(stats);
    
    switch (status) {
    case MSAT_SAT:
        printf("sat\n");
        break;
    case MSAT_UNSAT:
        printf("unsat\n");
        break;
    case MSAT_UNKNOWN:
        printf("unknown\n");
        break;
    }
    fflush(stdout);

    msat_destroy_env(env);

    if (e == DPLL_MINISAT) {
        deinit_minisat_solver(&me);
    } else {
        deinit_cleaneling_solver(&ce);
    }

    return 0;
}
