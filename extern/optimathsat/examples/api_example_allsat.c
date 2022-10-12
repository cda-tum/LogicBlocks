/*
 * api_example_allsat.c: A simple example of usage of the MathSAT "allsat" API
 * author: Alberto Griggio <griggio@fbk.eu>
 *
 * to compile: gcc api_example_allsat.c -I${MSAT_DIR}/include -L${MSAT_DIR}/lib
 *             -lmathsat -lgmpxx -lgmp -lstdc++ -o api_example_allsat
 */

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include "mathsat.h"

typedef struct MyData {
    msat_env env;
    msat_term dnf;
} MyData;

static int my_callback(msat_term *model, int size, void *user_data)
{
    MyData *data = (MyData *)user_data;
    msat_term cube = msat_make_true(data->env);
    int i;

    for (i = 0; i < size; ++i) {
        cube = msat_make_and(data->env, cube, model[i]);
    }
    data->dnf = msat_make_or(data->env, data->dnf, cube);

    return 1;
}


int main(void)
{
    msat_config cfg;
    msat_env env;
    int i;
    msat_term f;
    const char *vars[] = { "a", "b", "c", "d", "e", "f" };
    msat_term important[4];
    MyData data;

    cfg = msat_create_config();
    env = msat_create_env(cfg);
    msat_destroy_config(cfg);


    for (i = 0; i < 6; ++i) {
        msat_declare_function(env, vars[i],
                              msat_get_bool_type(env));
    }

    f = msat_from_string(env, "(and (or a b) (or c d) (or e f))");
    msat_assert_formula(env, f);

    data.env = env;
    data.dnf = msat_make_false(env);
    
    for (i = 0; i < 4; ++i) {
        important[i] = msat_from_string(env, vars[i]);
    }

    msat_all_sat(env, important, 4, my_callback, &data);

    printf("Got DNF:\n");
    msat_to_smtlib2_file(env, data.dnf, stdout);
    printf("\n");

    msat_destroy_env(env);
    return 0;
}
