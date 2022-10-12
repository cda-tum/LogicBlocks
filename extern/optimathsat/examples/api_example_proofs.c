#include "mathsat.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>


static void ensure_size(char **arr, size_t *cursz, size_t newsz)
{
    if (newsz > *cursz) {
        *arr = (char *)realloc(*arr, newsz);
        memset(*arr + *cursz, 0, newsz - *cursz);
        *cursz = newsz;
    }
}


static int is_seen(char **seen, size_t *sz, msat_proof p)
{
    int id = msat_proof_id(p);
    ensure_size(seen, sz, id+1);

    return (*seen)[id];
}


static void set_seen(char **seen, size_t *sz, msat_proof p)
{
    int id = msat_proof_id(p);
    ensure_size(seen, sz, id+1);

    (*seen)[id] = 1;
}


static void print_proof_rec(msat_proof p, int indent,
                            char **seen, size_t *sz)
{
    int i, id;
    for (i = 0; i < indent; ++i) {
        putchar(' ');
    }

    id = msat_proof_id(p);
    
    if (is_seen(seen, sz, p)) {
        printf("@%d", id);
    } else {
        set_seen(seen, sz, p);

        printf("#%d ", id);
        if (msat_proof_is_term(p)) {
            char *s = msat_term_repr(msat_proof_get_term(p));
            printf("%s", s);
            msat_free(s);
        } else {
            putchar('(');
            printf("%s\n", msat_proof_get_name(p));
            size_t j;
            size_t arity = msat_proof_get_arity(p);
            for (j = 0; j < arity; ++j) {
                print_proof_rec(msat_proof_get_child(p, j), indent+2, seen, sz);
                putchar('\n');
            }
            for (i = 0; i < indent; ++i) {
                putchar(' ');
            }
            putchar(')');
        }
    }
}


static void print_proof(msat_proof p)
{
    char *seen = NULL;
    size_t sz = 0;

    print_proof_rec(p, 0, &seen, &sz);
    putchar('\n');
    fflush(stdout);

    if (seen) {
        free(seen);
    }
}


int main(int argc, const char **argv)
{
    msat_config cfg = msat_create_config();
    msat_set_option(cfg, "proof_generation", "true");
    msat_set_option(cfg, "preprocessor.toplevel_propagation", "false");
    msat_set_option(cfg, "preprocessor.simplification", "0");
    msat_set_option(cfg, "theory.bv.eager",  /* for BV, only the lazy */
                    "false");                /* solver is proof-producing */
    msat_set_option(cfg, "theory.fp.mode", "2");
    msat_env env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    msat_term f;
    if (argc == 2) {
        FILE *src = fopen(argv[1], "r");
        if (!src) {
            printf("Error opening %s\n", argv[1]);
            return 1;
        }
        f = msat_from_smtlib2_file(env, src);
        fclose(src);
    } else {
        f = msat_from_smtlib2(
            env,
            "(declare-fun x1 () Real)"
            "(declare-fun x2 () Real)"
            "(declare-fun x3 () Real)"
            "(declare-fun y1 () Real)"
            "(declare-fun y2 () Real)"
            "(declare-fun y3 () Real)"
            "(declare-fun b () Real)"
            "(declare-fun f (Real) Real)"
            "(declare-fun g (Real) Real)"
            "(declare-fun a () Bool)"
            "(declare-fun c () Bool)"
            "(assert (and a (= (+ (f y1) y2) y3) (<= y1 x1)))"
            "(assert (and (= x2 (g b)) (= y2 (g b)) (<= x1 y1) (< x3 y3)))"
            "(assert (= a (= (+ (f x1) x2) x3)))"
            "(assert (and (or a c) (not c)))");
    }
    assert(!MSAT_ERROR_TERM(f));
    msat_assert_formula(env, f);
    msat_result res = msat_solve(env);

    assert(res == MSAT_UNSAT);
    if (res == MSAT_UNSAT) {
        msat_proof_manager pm = msat_get_proof_manager(env);
        assert(!MSAT_ERROR_PROOF_MANAGER(pm));
        msat_proof p = msat_get_proof(pm);
        print_proof(p);
        msat_destroy_proof_manager(pm);
    }

    msat_destroy_env(env);

    return 0;
}
