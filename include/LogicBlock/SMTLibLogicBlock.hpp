#ifndef SMTLIBLOGIC_H
#define SMTLIBLOGIC_H

#include "LogicBlock.hpp"

#include <functional>
#include <iostream>
#include <map>
#include <memory>

using namespace logicbase;

enum class SMTLibLogic {
    QF_UF,
    QF_LRA,
    QF_LIA,
    QF_BV,
    QF_IDL,
    QF_RDL,
    QF_NIA,
    QF_NRA,
    QF_UFLRA,
    QF_UFLIA,
    QF_UFBV,
    QF_UFIDL,
    QF_UFRDL,
    QF_UFNIA,
    QF_UFNRA
};

class SMTLogicBlock: logicbase::LogicBlock {
protected:
    std::map<unsigned long long, std::string> constants;
    std::unordered_set<SMTLibLogic>           requiredLogics;
    std::ostream&                             out;
    void                                      internal_reset() override;

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

private:
    SMTLibLogic getLogicForTerm(const LogicTerm& a);
    void        collectVariables();
};

#endif
