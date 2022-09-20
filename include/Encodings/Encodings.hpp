/*
* This file is part of the MQT QMAP library which is released under the MIT license.
* See file README.md or go to https://iic.jku.at/eda/research/ibm_qx_mapping/ for more information.
*/

#ifndef QMAP_ENCODINGS_HPP
#define QMAP_ENCODINGS_HPP

#include "LogicBlock/LogicBlock.hpp"

#include <algorithm>
#include <cmath>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <utility>
#include <vector>

namespace encodings {

    using namespace logicbase;

    struct NestedVar {
        explicit NestedVar(const LogicTerm& var):
            var(var), list(){};
        NestedVar(const LogicTerm& var, std::vector<NestedVar> list):
            var(var), list(std::move(list)) {}
        LogicTerm              var = LogicTerm::noneTerm();
        std::vector<NestedVar> list;
    };

    struct WeightedVar {
        WeightedVar(const LogicTerm& var, int weight):
            var(var), weight(weight) {}
        LogicTerm var    = LogicTerm::noneTerm();
        int       weight = 0;
    };
    inline bool operator<(const WeightedVar& rhs, const WeightedVar& lhs) {
        return rhs.weight < lhs.weight;
    }
    inline bool operator==(const WeightedVar& rhs, const WeightedVar& lhs) {
        return rhs.weight == lhs.weight && rhs.var.getID() == lhs.var.getID();
    }

    enum class Type { Uninitialized,
                      AuxVar,
                      ProgramVar };
    struct SavedLit {
        SavedLit():
            type(Type::Uninitialized), var(LogicTerm::noneTerm()) {}
        SavedLit(Type type, const LogicTerm& var):
            type(type), var(var) {}
        Type      type = Type::Uninitialized;
        LogicTerm var  = LogicTerm::noneTerm();
    };

    LogicTerm atMostOneCmdr(const std::vector<NestedVar>& subords,
                            const LogicTerm& cmdrVar, LogicBlock* logic);

    LogicTerm exactlyOneCmdr(const std::vector<NestedVar>& subords,
                             const LogicTerm& cmdrVar, LogicBlock* logic);

    LogicTerm naiveExactlyOne(const std::vector<LogicTerm>& clauseVars);

    LogicTerm naiveAtMostOne(const std::vector<LogicTerm>& clauseVars);

    LogicTerm naiveAtLeastOne(const std::vector<LogicTerm>& clauseVars);

    LogicTerm atMostOneBiMander(const std::vector<LogicTerm>& vars, LogicBlock* logic);

    std::vector<NestedVar> groupVars(const std::vector<LogicTerm>& vars,
                                     std::size_t                   maxSize);
    std::vector<NestedVar> groupVarsAux(const std::vector<NestedVar>& vars,
                                        std::size_t                   maxSize);

    std::vector<std::vector<LogicTerm>>
    groupVarsBimander(const std::vector<LogicTerm>& vars, std::size_t groupCount);

    [[maybe_unused]] LogicTerm BuildBDD(const std::set<WeightedVar>&  inputLiterals,
                                        const std::vector<LogicTerm>& vars, int leq, LogicBlock* lb);
    LogicTerm                  BuildBDD(uint64_t index, int64_t curSum, int64_t maxSum, int64_t k,
                                        const std::vector<WeightedVar>& inputLiterals,
                                        const std::vector<LogicTerm>& vars, LogicTerm& formula,
                                        LogicTerm& trueLit, LogicBlock* lb);
} // namespace encodings
#endif //QMAP_ENCODINGS_HPP
