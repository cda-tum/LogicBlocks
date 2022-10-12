/*
 * Unsat core extractor for SMT problems using MathSAT and an external
 * group-oriented Boolean unsat core extractor.
 *
 * Based on the Lemma-Lifting approach described in the paper:
 * "Computing Small Unsatsisfiable Cores in Satisfiability Modulo Theories"
 * by A. Cimatti, A. Griggio and R. Sebastiani
 *
 * For more information on group-oriented unsat core extraction tools, see:
 *   http://satcompetition.org/2011/rules.pdf
 *   http://www.cril.univ-artois.fr/SAT11/results/results.php?idev=49
 *
 * Instructions:
 * 
 *  This program takes two arguments: a boolean unsat core extractor, and a
 *  path to a formula in either SMT-LIBv2 or SMT-LIBv1 format.  The boolean
 *  core extractor receives a GCNF problem on stdin, and is expected to
 *  produce output on stdout conforming to the above SAT'11 competition rules.
 *  For example, to use the "Muser2" tool
 *  (http://logos.ucd.ie/wiki/doku.php?id=muser) as a core extractor, the
 *  following wrapper script "muser2.sh" can be used:
 *
 *     #!/bin/sh
 *     /path/to/run-muser2 -grp /dev/stdin
 *     exit $?
 *
 * author: Alberto Griggio <griggio@fbk.eu>
 */

#include "mathsat.h"
#include <stdio.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <ctype.h>
#include <assert.h>
#include <time.h>

static int skip_ws(FILE *in)
{
    int c;
    while ((c = fgetc(in)) != EOF && isspace(c)) {}
    ungetc(c, in);
    return c;
}

static int parse_int(FILE *in, int *out)
{
    int neg = 0;
    int c;
    int val = 0;
    c = fgetc(in);
    if (c == EOF) {
        return 1;
    }
    if (c == '-') {
        neg = 1;
        c = fgetc(in);
    } else if (c == '+') {
        c = fgetc(in);
    }
    if (!isdigit(c)) {
        return 1;
    }
    while (isdigit(c)) {
        val = val * 10 + (c - '0');
        c = fgetc(in);
    }
    ungetc(c, in);
    if (neg) {
        val = -val;
    }
    *out = val;
    return 0;
}


static int match_input(FILE *in, const char *s)
{
    int c;
    while (*s && (c = fgetc(in)) != EOF) {
        if (c != *s) {
            return 0;
        }
        ++s;
    }
    return 1;
}


int call_external_core_extractor(int *cnf_in, int *groups_in_out,
                                 size_t *size_in_out,
                                 void *user_data)
{
    const char *path = (const char *)user_data;
    
    int fds_to[2];
    int fds_from[2];
    if (pipe(fds_to) != 0 || pipe(fds_from) != 0) {
        return 1;
    }

    pid_t pid = fork();

    if (pid < 0) {
        return 1;
    } else if (pid == 0) {
        /* child */
        close(fds_to[1]);
        dup2(fds_to[0], 0);

        close(fds_from[0]);
        dup2(fds_from[1], 1);

        execl(path, path, (char *)NULL);
        return 1;
    }

    close(fds_to[0]);
    FILE *to_child_file = fdopen(fds_to[1], "w");
    if (!to_child_file) {
        return 1;
    }
    
    close(fds_from[1]);
    FILE *from_child_file = fdopen(fds_from[0], "r");
    if (!from_child_file) {
        return 1;
    }

    /* generate the DIMACS gcnf */
    int nvars = 0;
    int n = 0;
    int i = 0;
    int maxgroup = 0;
    for (i = 0, n = 0; n < *size_in_out; ++i) {
        int l = labs(cnf_in[i]);
        if (l == 0) {
            ++n;
        } else if (l > nvars) {
            nvars = l;
        }
    }
    for (n = 0; n < *size_in_out; ++n) {
        if (groups_in_out[n] > maxgroup) {
            maxgroup = groups_in_out[n];
        }
    }
    fprintf(to_child_file, "p gcnf %d %d %d\n", nvars, *size_in_out,
            maxgroup);
    fprintf(to_child_file, "{%d} ", groups_in_out[0]);
    for (i = 0, n = 0; n < *size_in_out; ++i) {
        int l = cnf_in[i];
        fprintf(to_child_file, "%d ", l);
        if (l == 0) {
            ++n;
            fprintf(to_child_file, "\n");
            if (n < *size_in_out) {
                fprintf(to_child_file, "{%d} ", groups_in_out[n]);
            }
        }
    }
    fflush(to_child_file);
    fclose(to_child_file);

    /* read back the core */
    int idx = 0;
    size_t sz  = 0;
    int retval = -1;
    int status = 0;

    int c;
    while ((c = fgetc(from_child_file)) != EOF) {
        if (isspace(c)) {
            skip_ws(from_child_file);
        } else if (c == 's') {
            /* solution line. If not UNSATISFIABLE, then raise an error */
            skip_ws(from_child_file);
            if (!match_input(from_child_file, "UNSATISFIABLE")) {
                retval = 1;
                break;
            }
            skip_ws(from_child_file);
        } else if (c == 'v') {
            while (1) {
                int group;
                c = skip_ws(from_child_file);
                if (c == EOF) {
                    retval = 1;
                    break;
                }
                if (!isdigit(c)) {
                    break;
                }
                if (parse_int(from_child_file, &group) != 0) {
                    retval = 1;
                    break;
                }
                if (group == 0) {
                    retval = 0;
                    break;
                } else {
                    groups_in_out[idx++] = group;
                    ++sz;
                }
            }
            if (retval != -1) {
                break;
            }
        } else if (isspace(c)) {
            skip_ws(from_child_file);
        } else if (c == 'c') {
            /* skip comments */
            while ((c = fgetc(from_child_file)) != EOF && c != '\n') {}
        } else {
            /* error */
            retval = 1;
            break;
        }
    }
    *size_in_out = sz;

    fclose(from_child_file);
    waitpid(pid, &status, 0);
    status = WEXITSTATUS(status);
    if (retval == 0 && status != 0 &&
        status != 20 /* 20 is the exit status for UNSAT answers mandated by
                      * the SAT competition */) {
        retval = status;
    }

    return retval;
}


size_t assert_conjunctions(msat_env env, msat_term formula)
{
    if (msat_term_is_and(env, formula)) {
        size_t s1 = assert_conjunctions(env, msat_term_get_arg(formula, 0));
        size_t s2 = assert_conjunctions(env, msat_term_get_arg(formula, 1));
        return s1 + s2;
    } else {
        msat_assert_formula(env, formula);
        return 1;
    }
}


double get_time_sec()
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    double total = (double)tv.tv_sec + (double)tv.tv_usec / 1000000.0;
    return total;
}


int main(int argc, const char **argv)
{
    if (argc != 3) {
        fprintf(stderr, "usage: %s bool_core_extractor FORMULA\n\n"
                "where:\n"
                "- FORMULA can be in either SMT-LIBv1 or SMT-LIBv2 format\n"
                "- bool_core_extractor receives a DIMACS gcnf from stdin "
                "  and prints the list of groups in the unsat core to stdout\n",
                argv[0]);
        return 1;
    }

    int retval = 0;
    size_t orig_size = 0;
    double start, end;
    
    const char *path = argv[1];
    msat_config cfg = msat_create_config();
    msat_set_option(cfg, "unsat_core_generation", "2");
    msat_env env = msat_create_env(cfg);

    msat_term formula;
    start = get_time_sec();
    FILE *src = fopen(argv[2], "r");
    if (!src) {
        fprintf(stderr, "ERROR opening %s\n", argv[2]);
        goto end;
    }
    formula = msat_from_smtlib2_file(env, src);
    msat_result res;
    if (MSAT_ERROR_TERM(formula)) {
        if (fseek(src, 0, SEEK_SET) == -1) {
            fprintf(stderr, "ERROR: %s\n", msat_last_error_message(env));
            goto end;
        } else {
            formula = msat_from_smtlib1_file(env, src);
        }
    }
    fclose(src);
    if (MSAT_ERROR_TERM(formula)) {
        fprintf(stderr, "ERROR: %s\n", msat_last_error_message(env));
        goto end;
    }
    orig_size = assert_conjunctions(env, formula);
    res = msat_solve(env);

    end = get_time_sec();
    fprintf(stdout, ";; solving time: %.3f\n", end-start);
    fflush(stdout);
    start = end;
    
    if (res == MSAT_UNKNOWN) {
        fprintf(stderr, "ERROR: %s\n", msat_last_error_message(env));
    } else if (res == MSAT_SAT) {
        fprintf(stdout, ";; sat\n");
    } else {
        msat_term *core;
        size_t core_size;
        core = msat_get_unsat_core_ext(env, &core_size,
                                       call_external_core_extractor,
                                       (void *)path);
        if (core == NULL) {
            fprintf(stderr, "ERROR: %s\n", msat_last_error_message(env));
        } else {
            size_t i;
            end = get_time_sec();
            fprintf(stdout, ";; core extraction time: %.3f\n", end-start);
            fprintf(stdout, ";; core with %d / %d formulas\n", core_size,
                    orig_size);
            msat_term t = msat_make_true(env);
            for (i = 0; i < core_size; ++i) {
                t = msat_make_and(env, t, core[i]);
            }
            msat_to_smtlib2_file(env, t, stdout);
            msat_free(core);
        }
    }
    fflush(stdout);

  end:
    msat_destroy_env(env);
    msat_destroy_config(cfg);
    
    return retval;
}
