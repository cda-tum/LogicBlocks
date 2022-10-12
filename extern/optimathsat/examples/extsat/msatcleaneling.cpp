#include "cleaneling.h"
#include "msatcleaneling.h"
#include <iostream>
#include <assert.h>
#include <vector>

namespace {

inline cleaneling_dpll_engine *E(void *self)
{ return static_cast<cleaneling_dpll_engine *>(self); }

inline Cleaneling::AbstractSolver *S(void *self) { return E(self)->solver; }

} // namespace

extern "C" {

static int add_clause(void *self,
                      int *clause, int permanent, int during_callback)
{
    for (size_t i = 0; clause[i]; ++i) {
        S(self)->addlit(clause[i]);
    }
    S(self)->addlit(0);
    return 0;
}

static msat_result solve(void *self, int *assumptions,
                         int **out_conflicting_assumptions)
{
    if (assumptions[0] != 0) {
        return MSAT_UNKNOWN; // solving under assumptions not supported
    }
    Cleaneling::Status ret = S(self)->solve();
    static int confl = 0;
    // unsat core ignored for now...
    *out_conflicting_assumptions = &confl;
    switch (ret) {
    case Cleaneling::SATISFIABLE: return MSAT_SAT;
    case Cleaneling::UNSATISFIABLE: return MSAT_UNSAT;
    default: return MSAT_UNKNOWN;
    }
}

static msat_truth_value model_value(void *self, int lit)
{
    assert(lit > 0);
    Cleaneling::Value res = S(self)->value(lit);
    switch (res) {
    case Cleaneling::UNASSIGNED: return MSAT_UNDEF;
    case Cleaneling::FALSE: return MSAT_FALSE;
    case Cleaneling::TRUE: return MSAT_TRUE;
    }
}

static int set_decision_var(void *self, int var, int yes)
{
    return 0;
}

static int set_frozen(void *self, int var, int yes)
{
    assert(var >= 1);
    if (yes && E(self)->melted[var-1]) {
        S(self)->freeze(var);
    } else if(!yes && !(E(self)->melted[var-1])) {
        S(self)->melt(var);
    }
    return 0;
}

static int new_var(void *self)
{
    E(self)->melted.push_back(true);
    return ++(E(self)->next_var);
}

static int enqueue_assignment(void *self, int lit)
{
    S(self)->external_assign(lit);
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
    E(self)->melted.clear();
    E(self)->next_var = 0;
    E(self)->solver = Cleaneling::new_solver();
    return 0;
}

static int set_callback(void *self, msat_dpll_callback cb)
{
    S(self)->set_msat_dpll_callback(cb);
    return 0;
}


void init_cleaneling_solver(cleaneling_dpll_engine *engine)
{
    engine->solver = Cleaneling::new_solver();
    engine->solver->option("verbose", 1);
    engine->solver->option("distill", 0);
    engine->solver->option("elim", 0);
    engine->solver->option("block", 0);
    
    engine->next_var = 0;
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

void deinit_cleaneling_solver(cleaneling_dpll_engine *engine)
{
    delete engine->solver;
}


} // extern "C"
