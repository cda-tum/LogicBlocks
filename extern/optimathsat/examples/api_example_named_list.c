/*
 * api_example_named_list.c: A simple example of usage of the MathSAT API
 *                           functions msat_named_list_from_smtlib2 and
 *                           msat_named_list_to_smtlib2
 *                           
 * author: Alberto Griggio <griggio@fbk.eu>
 *
 * to compile: gcc api_example_named_list.c -I${MSAT_DIR}/include
 *             -L${MSAT_DIR}/lib -lmathsat -lgmpxx -lgmp -lstdc++
 *             -o api_example_named_list
 */


#include <stdio.h>
#include "mathsat.h"


int main(int argc, const char **argv)
{
    msat_config cfg = msat_create_config();
    msat_env env = msat_create_env(cfg);

    msat_term x = msat_make_constant(
        env, msat_declare_function(env, "x", msat_get_integer_type(env)));
    msat_term y = msat_make_constant(
        env, msat_declare_function(env, "y", msat_get_rational_type(env)));
    msat_term a = msat_make_constant(
        env, msat_declare_function(env, "a", msat_get_bool_type(env)));

    const char *names[5] = { "T1", "T2", "T3", "T4", "T5" };
    msat_term terms[5];
    terms[0] = x;
    terms[1] = y;
    terms[2] = a;
    terms[3] = msat_make_equal(env, x, y);
    terms[4] = msat_make_iff(env, a, msat_make_leq(env, x, y));

    char *data = msat_named_list_to_smtlib2(env, 5, names, terms);

    msat_env e2 = msat_create_env(cfg);
    char **names2;
    msat_term *terms2;
    size_t n;

    int ok = msat_named_list_from_smtlib2(e2, data, &n, &names2, &terms2);
    if (ok == 0) {
        printf("OK, got the following:\n");
        size_t i;
        for (i = 0; i < n; ++i) {
            char *s = msat_term_repr(terms2[i]);
            printf(" %s := %s\n", names2[i], s);
            msat_free(s);
            msat_free(names2[i]);
        }
        msat_free(names2);
        msat_free(terms2);
    } else {
        printf("ERROR: %s\n", msat_last_error_message(e2));
    }

    msat_free(data);

    fflush(stdout);

    msat_destroy_env(e2);
    msat_destroy_env(env);
    msat_destroy_config(cfg);    
    return 0;
}
