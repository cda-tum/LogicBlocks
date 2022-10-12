/*
 * api_example_lowlevel.cpp: A simple example of usage of the MathSAT
 *                           low-level API
 * author: Alberto Griggio <griggio@fbk.eu>
 *
 * to compile: g++ api_example.c -I${MSAT_DIR}/include -L${MSAT_DIR}/lib
 *             -lmathsat -lgmpxx -lgmp -lstdc++ -o api_example
 */

#include "mathsatll.h"
#include <iostream>
#include <map>
#include <cstdlib>
#include <cctype>

typedef std::map<int, msat_satvar> VarMap;

msat_satlit mklit(msat_ll_solver dpll, VarMap &vmap, int lit)
{
    int v = std::abs(lit);
    VarMap::iterator it = vmap.find(v);
    msat_satvar sv = msat_satvar_undef;
    if (it != vmap.end()) {
        sv = it->second;
    } else {
        sv = msat_ll_make_var(dpll);
        vmap[v] = sv;
    }
    return msat_make_satlit(sv, lit < 0);
}


int main()
{
    // example parsing a DIMACS file from stdin and using MathSAT as a plain
    // SAT solver
    msat_config cfg = msat_create_config();
    // set some config settings that are good for SAT
    msat_set_option(cfg, "dpll.restart_strategy", "3");
    msat_set_option(cfg, "dpll.glucose_learnt_minimization", "true");
    msat_set_option(cfg, "dpll.glucose_var_activity", "true");
    msat_set_option(cfg, "dpll.branching_random_frequency", "0");
    msat_set_option(cfg, "verbosity", "2");

    msat_env env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    msat_ll_solver dpll =
        msat_create_ll_solver(env, false /* no theory support */);

    VarMap vmap;
    char c;
    bool ok = true;
    size_t nclauses = 0;
    
    // parse DIMACS from stdin
    while (ok && std::cin.get(c)) {
        switch (c) {
        case 'c':
        case 'p':
            while (std::cin.get(c) && c != '\n') {}
        break;
        default:
            if (!std::isdigit(c) && c != '-') {
                ok = false;
            } else {
                std::cin.putback(c);
                int lit;
                msat_ll_begin_clause(dpll);
                ok = false;
                while (std::cin >> lit) {
                    if (!lit) {
                        msat_ll_end_clause(dpll);
                        ++nclauses;
                        ok = true;
                        while (std::cin.get(c)) {
                            if (!std::isspace(c)) {
                                std::cin.putback(c);
                                break;
                            }
                        }
                        break;
                    } else {
                        msat_satlit l = mklit(dpll, vmap, lit);
                        msat_ll_addlit(dpll, l);
                    }
                }
            }
        }
    }

    if (!ok) {
        std::cerr << "Error parsing input" << std::endl;
    } else {
        std::cout << "c parsed problem with " << vmap.size()
                  << " vars and " << nclauses << " clauses" << std::endl;
        msat_result res = msat_ll_solve(dpll, NULL, 0);

        char *stats = msat_ll_get_search_stats(dpll);
        if (stats) {
            std::cout << "c STATISTICS:\n";
            std::cout << stats << std::endl;
            msat_free(stats);
        }
        
        std::cout << "s " << (res == MSAT_SAT ? "SATISFIABLE" :
                              (res == MSAT_UNSAT ? "UNSATISFIABLE" :
                               "UNKNOWN"))
                  << std::endl;
        if (res == MSAT_SAT) {
            std::cout << "v";
            for (VarMap::iterator it = vmap.begin(), end = vmap.end();
                 it != end; ++it) {
                int v = it->first;
                msat_satvar sv = it->second;
                msat_truth_value val = msat_ll_get_model_value(dpll, sv);
                switch (val) {
                case MSAT_FALSE:
                    std::cout << " -" << v;
                    break;
                case MSAT_TRUE:
                    std::cout << " " << v;
                    break;
                default:
                    break;
                }
            }
            std::cout << std::endl;
        }
    }
    
    msat_destroy_ll_solver(dpll);
    msat_destroy_env(env);

    return ok ? 0 : -1;
}
