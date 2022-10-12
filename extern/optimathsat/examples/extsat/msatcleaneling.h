#include "mathsat.h"
#include <vector>

namespace Cleaneling { class AbstractSolver; }

extern "C" {

struct cleaneling_dpll_engine {
    msat_ext_dpll_interface iface;
    Cleaneling::AbstractSolver *solver;
    int next_var;
    std::vector<bool> melted;
};


void init_cleaneling_solver(cleaneling_dpll_engine *engine);
void deinit_cleaneling_solver(cleaneling_dpll_engine *engine);

}
