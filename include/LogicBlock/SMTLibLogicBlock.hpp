#ifndef SMTLIBLOGIC_H
#define SMTLIBLOGIC_H

#include "LogicBlock.hpp"

#include <functional>
#include <iostream>
#include <map>
#include <memory>

using namespace logicbase;

enum class SMTLibLogic {
    NONE,
    QF_UF,
    QF_BV,
    QF_IDL,
    QF_RDL,
    QF_LRA,
    QF_LIA,
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

class SMTLogicBlock: public logicbase::LogicBlock {
protected:
    std::map<unsigned long long, LogicTerm> constants;
    std::unordered_set<SMTLibLogic>         requiredLogics;
    SMTLibLogic                             outputLogic;
    std::ostream&                           out;
    void                                    internal_reset() override;

public:
    explicit SMTLogicBlock(bool convertWhenAssert = false, std::ostream& out = std::cout):
        logicbase::LogicBlock(convertWhenAssert), out(out) {}

    void   assertFormula(const LogicTerm& a) override;
    void   produceInstance() override;
    Result solve() override;
    void   reset() override {
        delete model;
        model = nullptr;
        clauses.clear();
        internal_reset();
        gid = 0;
    };

    void setOutputLogic(SMTLibLogic logic) { outputLogic = logic; }
    void addRequiredLogic(SMTLibLogic logic) { requiredLogics.insert(logic); }

private:
    SMTLibLogic        getLogicForTerm(const LogicTerm& a);
    static SMTLibLogic getMinimumLogic(const SMTLibLogic& a, const SMTLibLogic& b);

    void               collectVariables(const LogicTerm& a);
    static std::string getConstantString(const LogicTerm& a);
    static std::string getTypeString(const LogicTerm& a);

    static std::string writeConstantDefinition(const LogicTerm& a);

    static std::string writeLogicDefinition(const SMTLibLogic& logic);

    std::string convert(const LogicTerm& a);
};

#endif
