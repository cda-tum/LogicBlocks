#include "msatminisat.h"
#include "core/Solver.h"
#include <iostream>
#include <stdlib.h>
#include <vector>

namespace {

inline minisat_dpll_engine *E(void *self)
{ return static_cast<minisat_dpll_engine *>(self); }

inline Minisat::Solver *S(void *self) { return E(self)->solver; }

inline Minisat::Lit dimacs2lit(int assignment)
{
    assert(assignment);
    Minisat::Var x = (assignment < 0 ? -assignment : assignment) - 1;
    return Minisat::mkLit(x, assignment < 0);
}


inline void translate2lits(int *dimacs,
                           Minisat::vec<Minisat::Lit>& lits)
{
    assert(lits.size() == 0);
    assert(dimacs);
    for (size_t i = 0; dimacs[i]; ++i) {
        lits.push(dimacs2lit(dimacs[i]));
    }
}

} // namespace


extern "C" {

static int add_clause(void *self,
                      int *clause, int permanent, int during_callback)
{
    Minisat::vec<Minisat::Lit> lits;
    translate2lits(clause, lits);
    S(self)->addClause(lits);
    return 0;
}

static msat_result solve(void *self, int *assumptions,
                         int **out_conflicting_assumptions)
{
    Minisat::vec<Minisat::Lit> ass;
    translate2lits(assumptions, ass);
    bool sat = S(self)->solve(ass);
    int confl = 0;
    // unsat core ignored for now...
    *out_conflicting_assumptions = &confl;
    return sat ? MSAT_SAT : MSAT_UNSAT;
}

static msat_truth_value model_value(void *self, int lit)
{
    Minisat::Lit l = dimacs2lit(lit);
    using Minisat::lbool;
    lbool v = S(self)->value(l);
    if (v == l_True) {
        return MSAT_TRUE;
    } else if (v == l_False) {
        return MSAT_FALSE;
    } else {
        return MSAT_UNDEF;
    }
}

static int set_decision_var(void *self, int var, int yes)
{
    return 0;
}

static int set_frozen(void *self, int var, int yes)
{
    return 0;
}

static int new_var(void *self)
{
    return (S(self)->newVar() + 1);
}

static int enqueue_assignment(void *self, int lit)
{
    Minisat::Lit l = dimacs2lit(lit);
    S(self)->uncheckedEnqueue(l);
    return 0;
}

static int remove_clauses_containing(void *self, int v)
{
    assert(v >= 0);
    std::vector<int> unit_clause_deleting_satisfied_clauses;
    unit_clause_deleting_satisfied_clauses.push_back(-v);
    unit_clause_deleting_satisfied_clauses.push_back(0);
    return add_clause(self, &(unit_clause_deleting_satisfied_clauses[0]),
                      true, false);
}

static int reset(void *self)
{
    delete S(self);
    E(self)->solver = new Minisat::Solver();
    return 0;
}

static int set_callback(void *self, msat_dpll_callback cb)
{
    S(self)->event = cb;
    S(self)->has_event = true;
    return 0;
}

void init_minisat_solver(minisat_dpll_engine *engine)
{
    engine->solver = new Minisat::Solver();
    engine->iface.add_clause = add_clause;
    engine->iface.solve = solve;
    engine->iface.model_value = model_value;
    engine->iface.set_decision_var = set_decision_var;
    engine->iface.set_frozen = set_frozen;
    engine->iface.new_var = new_var;
    engine->iface.enqueue_assignment = enqueue_assignment;
    engine->iface.remove_clauses_containing = remove_clauses_containing;
    engine->iface.reset = reset;
    engine->iface.set_callback = set_callback;
}

void deinit_minisat_solver(minisat_dpll_engine *engine)
{
    delete engine->solver;
}

} // extern "C"

