#include "LogicBlock/SMTLibLogicBlock.hpp"

void SMTLogicBlock::produceInstance() {
    out << "" << std::endl;
}

Result SMTLogicBlock::solve() {
    return Result::SAT;
}

void SMTLogicBlock::internal_reset() {
    delete model;
    model = nullptr;
}
