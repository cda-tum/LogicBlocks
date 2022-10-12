#include "mathsat.h"

namespace Minisat { class Solver; }

extern "C" {

struct minisat_dpll_engine {
    msat_ext_dpll_interface iface;
    Minisat::Solver *solver;
};


void init_minisat_solver(minisat_dpll_engine *engine);
void deinit_minisat_solver(minisat_dpll_engine *engine);

} // extern "C"
