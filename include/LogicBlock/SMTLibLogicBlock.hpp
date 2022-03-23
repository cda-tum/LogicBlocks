#ifndef SMTLIBLOGIC_H
#define SMTLIBLOGIC_H

#include "LogicBlock.hpp"

#include <functional>
#include <iostream>
#include <map>
#include <memory>

using namespace logicbase;
class SMTLogicBlock: logicbase::LogicBlock {
protected:
    std::ostream& out;
    void          internal_reset() override;

public:
    explicit SMTLogicBlock(bool convertWhenAssert = false, std::ostream& out = std::cout):
        logicbase::LogicBlock(convertWhenAssert), out(out) {}

    void   produceInstance() override;
    Result solve() override;
    void   reset() override {
        delete model;
        model = nullptr;
        clauses.clear();
        internal_reset();
        gid = 0;
    };
};

#endif
