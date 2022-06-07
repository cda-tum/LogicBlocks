//
// Created by Sarah on 30.05.2022.
//
#include "LogicBlock/CNFLogicBlock.hpp"
#include "utils/logging.hpp"

void CNFLogicBlock::internal_reset() {
    delete model;
    model = nullptr;
}
void CNFLogicBlock::produceInstance() {

    out << "" << std::endl;
}
Result CNFLogicBlock::solve() {
    return Result::UNSAT;
}
void CNFLogicBlock::dump(const LogicTerm& a, std::ostream& stream) {
    LogicBlock::dump(a, stream);
}
void CNFLogicBlock::dumpAll(std::ostream& stream) {
    LogicBlock::dumpAll(stream);
}
void CNFLogicBlock::assertFormula(const LogicTerm& a) {
    if (a.getOpType() == OpType::AND) {
        for (const auto& clause: a.getNodes()) {
            clauses.insert(clause);
        }
    } else {
        clauses.insert(a);
    }
    if (convertWhenAssert){
        convert();
    }
}
void CNFLogicBlock::convert() {
}
