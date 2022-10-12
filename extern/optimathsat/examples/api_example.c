/*
 * api_example.c: A simple example of usage of the MathSAT API
 * author: Alberto Griggio <griggio@fbk.eu>
 *
 * to compile: gcc api_example.c -I${MSAT_DIR}/include -L${MSAT_DIR}/lib
 *             -lmathsat -lgmpxx -lgmp -lstdc++ -o api_example
 */

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include "mathsat.h"


static void example1();
static void example_interpolation1();
static void example_interpolation2();
static void example_unsat_core();

int main()
{
    printf("MathSAT API Examples\n");

    printf("Press RETURN to begin...\n");
    getchar();
    example1();

    printf("Press RETURN to continue...\n");
    getchar();
    example_interpolation1();

    printf("Press RETURN to continue...\n");
    getchar();
    example_interpolation2();

    printf("Press RETURN to continue...\n");
    getchar();
    example_unsat_core();
    
    return 0;
}


static msat_term create_a_formula(msat_env env)
{
    const char *vn[] = {"v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8"};
    msat_decl vars[sizeof(vn)/sizeof(vn[0])];
    const char *fn[] = {"f", "h"};
    msat_decl funcs[sizeof(fn)/sizeof(fn[0])];
    unsigned int i;
    msat_term res, tmp;
    msat_type rat_tp, func_tp;
    msat_type paramtps[1];

    /* get the rat type (aka sort) */
    rat_tp = msat_get_rational_type(env);
    assert(!MSAT_ERROR_TYPE(rat_tp));
    
    /* first, let's declare the functions we are going to use */
    for (i = 0; i < sizeof(vn)/sizeof(vn[0]); ++i) {
        vars[i] = msat_declare_function(env, vn[i], rat_tp);
        assert(!MSAT_ERROR_DECL(vars[i]));
    }

    /* create the type for the functions */
    paramtps[0] = rat_tp;
    func_tp = msat_get_function_type(env, paramtps, 1, rat_tp);
    assert(!MSAT_ERROR_TYPE(func_tp));
    
    for (i = 0; i < sizeof(fn)/sizeof(fn[0]); ++i) {
        funcs[i] = msat_declare_function(env, fn[i], func_tp);
        assert(!MSAT_ERROR_DECL(funcs[i]));
    }

    /* we can create terms in two ways. The easiest one is by using
     * msat_from_string. The syntax is that of SMT-LIBv2 */
    res = msat_from_string(
        env, "(and (= v3 (h v0)) (= v4 (h v1)) (= v6 (f v2)) (= v7 (f v5)))");
    assert(!MSAT_ERROR_TERM(res));

    /* the other one is by using the various msat_make_* functions */
    tmp = msat_make_leq(env,
                        msat_make_constant(env, vars[1]),
                        msat_make_constant(env, vars[0]));
    res = msat_make_and(env, res, tmp);
    tmp = msat_make_not(env,
                        msat_make_equal(env,
                                        msat_make_constant(env, vars[6]),
                                        msat_make_constant(env, vars[7])));
    res = msat_make_and(env, res, tmp);
    tmp = msat_from_string(env, "(and (<= v0 v1) (= v2 (- v3 v4)))");
    res = msat_make_and(env, res, tmp);

    return res;
}


static void print_model(msat_env env)
{
    /* we use a model iterator to retrieve the model values for all the
     * variables, and the necessary function instantiations */
    msat_model_iterator iter = msat_create_model_iterator(env);
    assert(!MSAT_ERROR_MODEL_ITERATOR(iter));

    printf("Model:\n");
    while (msat_model_iterator_has_next(iter)) {
        msat_term t, v;
        char *s;
        msat_model_iterator_next(iter, &t, &v);
        s = msat_term_repr(t);
        assert(s);
        printf(" %s = ", s);
        msat_free(s);
        s = msat_term_repr(v);
        assert(s);
        printf("%s\n", s);
        msat_free(s);
    }
    msat_destroy_model_iterator(iter);
}


/* 
 * This example shows the basic usage of the API for creating formulas,
 * checking satisfiability, and using the solver incrementally
 */ 
static void example1()
{
    msat_config cfg;
    msat_env env;
    msat_term formula;
    msat_result status;
    int res;
    char *s;

    printf("\nExample 1\n");

    /* first, we create a configuration */
    cfg = msat_create_config();
    /* enable model generation */
    msat_set_option(cfg, "model_generation", "true");

    /* create an environment with the above configuration */
    env = msat_create_env(cfg);

    /* create a formula and assert it permanently */
    formula = create_a_formula(env);
    res = msat_assert_formula(env, formula);
    assert(res == 0);

    s = msat_term_repr(formula);
    assert(s);
    printf("Asserted: %s\n", s);
    msat_free(s);

    /* incrementally add an assertion */
    res = msat_push_backtrack_point(env);
    assert(res == 0);
    formula = msat_from_string(env, "(= v5 0)");
    assert(!MSAT_ERROR_TERM(formula));
    res = msat_assert_formula(env, formula);
    assert(res == 0);

    s = msat_term_repr(formula);
    assert(s);
    printf("Added constraint: %s\n", s);

    /* check satisfiability */
    status = msat_solve(env);
    assert(status == MSAT_UNSAT);

    printf("Environment is inconsistent, retracting constraint %s\n", s);

    /* retract the assertion and try again with another one */
    res = msat_pop_backtrack_point(env);
    assert(res == 0);
    res = msat_push_backtrack_point(env);
    assert(res == 0);
    formula = msat_from_string(env, "(= v5 v8)");
    assert(!MSAT_ERROR_TERM(formula));
    res = msat_assert_formula(env, formula);
    assert(res == 0);

    msat_free(s);
    s = msat_term_repr(formula);
    assert(s);
    printf("Added constraint: %s\n", s);
    msat_free(s);

    status = msat_solve(env);
    assert(status == MSAT_SAT);

    printf("Environment is now consistent, getting the model...\n");
    
    /* display the model */
    print_model(env);

    msat_destroy_env(env);
    msat_destroy_config(cfg);

    printf("\nExample 1 done\n");
}


/* 
 * this example shows how to generate an interpolant for the following pair of
 * formulas:
 * A = (and (= (+ (f x1) x2) x3) (= (+ (f y1) y2) y3) (<= y1 x1))
 * B = (and (= x2 (g b)) (= y2 (g b)) (<= x1 y1) (< x3 y3))
 */
static void example_interpolation1()
{
    msat_config cfg;
    msat_env env;
    msat_term formula;
    const char *vars[] = {"x1", "x2", "x3", "y1", "y2", "y3", "b"};
    const char *ufs[] = {"f", "g"};
    unsigned int i;
    int res, group_a, group_b;
    msat_type rat_tp, func_tp;
    msat_type paramtps[1];

    printf("\nInterpolation example\n");

    cfg = msat_create_config();
    /* enable interpolation support */
    msat_set_option(cfg, "interpolation", "true");
    
    env = msat_create_env(cfg);
    assert(!MSAT_ERROR_ENV(env));

    /* the configuration can be deleted as soon as the evironment has been
     * created */
    msat_destroy_config(cfg);

    rat_tp = msat_get_rational_type(env);
    paramtps[0] = rat_tp;
    func_tp = msat_get_function_type(env, paramtps, 1, rat_tp);

    /* declare variables/functions */
    for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
        msat_decl d = msat_declare_function(env, vars[i], rat_tp);
        assert(!MSAT_ERROR_DECL(d));
    }
    for (i = 0; i < sizeof(ufs)/sizeof(ufs[0]); ++i) {
        msat_decl d = msat_declare_function(env, ufs[i], func_tp);
        assert(!MSAT_ERROR_DECL(d));
    }

    /* now create the interpolation groups representing the two formulas A and
     * B */
    group_a = msat_create_itp_group(env);
    group_b = msat_create_itp_group(env);
    assert(group_a != -1 && group_b != -1);
    
    /* create and assert formula A */
    formula = msat_from_string(
        env, "(and (= (+ (f x1) x2) x3) (= (+ (f y1) y2) y3) (<= y1 x1))");
    assert(!MSAT_ERROR_TERM(formula));

    /* tell MathSAT that all subsequent formulas belong to group A */
    res = msat_set_itp_group(env, group_a);
    assert(res == 0);
    res = msat_assert_formula(env, formula);
    assert(res == 0);
    {
        char *s = msat_term_repr(formula);
        assert(s);
        printf("Asserted formula A (in group %d): %s\n", group_a, s);
        msat_free(s);
    }

    /* create and assert formula B */
    formula = msat_from_string(
        env, "(and (= x2 (g b)) (= y2 (g b)) (<= x1 y1) (< x3 y3))");
    assert(!MSAT_ERROR_TERM(formula));

    /* tell MathSAT that all subsequent formulas belong to group B */
    res = msat_set_itp_group(env, group_b);
    assert(res == 0);
    res = msat_assert_formula(env, formula);
    assert(res == 0);
    {
        char *s = msat_term_repr(formula);
        assert(s);
        printf("Asserted formula B (in group %d): %s\n", group_b, s);
        msat_free(s);
    }

    if (msat_solve(env) == MSAT_UNSAT) {
        int groups_of_a[1];
        msat_term interpolant;
        char *s;
        groups_of_a[0] = group_a;
        interpolant = msat_get_interpolant(env, groups_of_a, 1);
        assert(!MSAT_ERROR_TERM(interpolant));
        s = msat_term_repr(interpolant);
        assert(s);
        printf("\nOK, the interpolant is: %s\n", s);
        msat_free(s);
    } else {
        assert(0 && "should not happen!");
    }

    msat_destroy_env(env);

    printf("\nInterpolation example 1 done\n");
}


static void example_interpolation2()
{
    msat_config cfg;
    const char *a_part;
    const char *b_part_1;
    const char *b_part_2;
    msat_env env;
    msat_term fa, fb1, fb2, itp;
    msat_result res;
    int ia, ib1, ib2; 
    char *s;
    int ga[1];

    cfg = msat_create_config();
    msat_set_option(cfg, "interpolation", "true");

    a_part =
        "(declare-fun x () Bool)"
        "(declare-fun y () Bool)"
        "(declare-fun z () Bool)"
        "(assert (and (or x y) (or (not y) x) (or (not x) z)))";

    b_part_1 =
        "(declare-fun z () Bool)"
        "(declare-fun w () Bool)"
        "(declare-fun v () Bool)"
        "(assert (and (or w v (not z)) (or (not w) v) (not v)))";

    b_part_2 = 
        "(declare-fun z () Bool)"
        "(declare-fun x () Bool)"
        "(declare-fun v () Bool)"
        "(assert (and (or v (not z) (not x)) (or (not v) (not z))))";

    env = msat_create_env(cfg);

    fa = msat_from_smtlib2(env, a_part);
    fb1 = msat_from_smtlib2(env, b_part_1);

    ia = msat_create_itp_group(env);
    msat_set_itp_group(env, ia);
    msat_assert_formula(env, fa);

    msat_push_backtrack_point(env);
    ib1 = msat_create_itp_group(env);
    msat_set_itp_group(env, ib1);
    msat_assert_formula(env, fb1);

    res = msat_solve(env);
    assert(res == MSAT_UNSAT);

    ga[0] = ia;

    itp = msat_get_interpolant(env, ga, 1);
    assert(!MSAT_ERROR_TERM(itp));

    s = msat_to_smtlib2(env, itp);
    printf("Got interpolant 1:\n%s\n", s);
    msat_free(s);

    msat_pop_backtrack_point(env);
    msat_push_backtrack_point(env);

    fb2 = msat_from_smtlib2(env, b_part_2);
    ib2 = msat_create_itp_group(env);
    msat_set_itp_group(env, ib2);
    msat_assert_formula(env, fb2);

    res = msat_solve(env);
    assert(res == MSAT_UNSAT);

    itp = msat_get_interpolant(env, ga, 1);
    assert(!MSAT_ERROR_TERM(itp));

    s = msat_to_smtlib2(env, itp);
    printf("Got interpolant 2:\n%s\n", s);
    msat_free(s);

    msat_destroy_env(env);
    msat_destroy_config(cfg);

    printf("Interpolation example 2 done\n");
}


void example_unsat_core()
{
    msat_config cfg;
    msat_env env;
    msat_decl x, y;
    msat_term a, b, c, t;
    msat_result res;
    msat_term *core;
    size_t i, core_size;
    char *s;
    
    cfg = msat_create_config();
    /* enable unsat core generation */
    msat_set_option(cfg, "unsat_core_generation", "1");
    
    env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    x = msat_declare_function(env, "x", msat_get_rational_type(env));
    y = msat_declare_function(env, "y", msat_get_rational_type(env));

    a = msat_from_string(env, "(not (> x 2))");
    b = msat_from_string(env, "(> x 3)");
    c = msat_from_string(env, "(> (+ x y) 0)");

    /* compute an unsat core as a subset of the asserted formulas */
    /* first, we assert the three constraints individually */
    msat_assert_formula(env, a);
    s = msat_term_repr(a);
    printf("asserted: %s, id: %d\n", s, msat_term_id(a));
    msat_free(s);
    
    msat_assert_formula(env, b);
    s = msat_term_repr(b);
    printf("asserted: %s, id: %d\n", s, msat_term_id(b));
    msat_free(s);

    msat_assert_formula(env, c);
    s = msat_term_repr(c);
    printf("asserted: %s, id: %d\n", s, msat_term_id(c));
    msat_free(s);

    res = msat_solve(env);

    assert(res == MSAT_UNSAT);
    
    /* get the unsat core */
    core = msat_get_unsat_core(env, &core_size);

    if (core == NULL) {
        printf("error in computing the unsat core\n");
    } else {
        printf("the unsat core is:\n");
        for (i = 0; i < core_size; ++i) {
            t = core[i];
            s = msat_term_repr(t);
            printf(" %s, id: %d\n", s, msat_term_id(t));
            msat_free(s);
        }
        msat_free(core);
    }

    msat_destroy_env(env);

    printf("Unsat core example done\n");
}
