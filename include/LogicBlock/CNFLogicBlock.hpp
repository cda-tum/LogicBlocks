//
// Created by Sarah on 30.05.2022.
//

#ifndef LOGICBLOCKS_CNFLOGICBLOCK_H
#define LOGICBLOCKS_CNFLOGICBLOCK_H

#include "LogicBlock.hpp"

#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <unordered_set>

using namespace logicbase;

class CNFLogicBlock: logicbase::LogicBlock {
protected:
    std::ostream&                                                        out;
    void                                                                 internal_reset() override;
    std::unordered_set<std::unordered_set<long long>, UnorderedLongHash> convertedClauses{};

public:
    explicit CNFLogicBlock(bool convertWhenAssert = false, std::ostream& out = std::cout):
        logicbase::LogicBlock(convertWhenAssert), out(out) {}

    void   produceInstance() override;
    Result solve() override;

    void dump(const LogicTerm& a, std::ostream& stream) override;
    void dumpAll(std::ostream& stream) override;

    void assertFormula(const LogicTerm& a) override;

    void convert();

    void reset() override {
        delete model;
        model = nullptr;
        clauses.clear();
        internal_reset();
        gid = 0;
    };
};

#endif //LOGICBLOCKS_CNFLOGICBLOCK_H
