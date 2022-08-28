#ifndef UTIL_LOGICBLOCK_H
#define UTIL_LOGICBLOCK_H

#include "LogicBlock/LogicBlock.hpp"
#include "LogicBlock/SMTLibLogicBlock.hpp"
#include "LogicBlock/Z3Logic.hpp"
#include "LogicTerm/Logic.hpp"

#ifdef Z3_FOUND
    #include <z3++.h>
    #include <z3_api.h>
#endif

namespace logicutil {
    using namespace logicbase;

    inline std::unique_ptr<LogicBlock> getZ3LogicBlock(bool convertWhenAssert, std::vector<std::pair<std::string, std::string>>& s_params, std::vector<std::pair<std::string, bool>>& b_params, std::vector<std::pair<std::string, int>>& int_params) {
#ifdef Z3_FOUND
        z3::context c;
        z3::solver  slv(c);
        z3::params  p(c);

        slv.set(p);
        return std::make_unique<z3logic::Z3LogicBlock>(c, slv, convertWhenAssert);
#else
        throw std::runtime_error("Z3 not found");
#endif
    }

    inline std::unique_ptr<LogicBlockOptimizer> getZ3LogicOptimizer(bool convertWhenAssert, std::vector<std::pair<std::string, std::string>>& s_params, std::vector<std::pair<std::string, bool>>& b_params, std::vector<std::pair<std::string, int>>& int_params) {
#ifdef Z3_FOUND
        z3::context  c;
        z3::optimize opt(c);
        z3::params   p(c);

        opt.set(p);
        return std::make_unique<z3logic::Z3LogicOptimizer>(c, opt, convertWhenAssert);
#else
        throw std::runtime_error("Z3 not found");
#endif
    }
} // namespace logicutil

#endif //UTIL_LOGICBLOCK_H
