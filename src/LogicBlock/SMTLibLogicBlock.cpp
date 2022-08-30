#include "LogicBlock/SMTLibLogicBlock.hpp"

#include "LogicUtil/util_logic.hpp"

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
SMTLibLogic SMTLogicBlock::getLogicForTerm(const LogicTerm& a) {
    using namespace logicutil;
    switch (a.getOpType()) {
        case OpType::Variable:
        case OpType::Constant:
            switch (a.getCType()) {
                case CType::BOOL:
                    return SMTLibLogic::QF_UF;
                case CType::INT:
                    return SMTLibLogic::QF_LIA;
                case CType::REAL:
                    return SMTLibLogic::QF_LRA;
                case CType::BITVECTOR:
                    return SMTLibLogic::QF_BV;
                default:
                    throw std::runtime_error("Unsupported CType");
            }
            break;
        case OpType::NEG: {
        }
        default:
            return SMTLibLogic::QF_UFNRA;
    }

    return SMTLibLogic::QF_UFNRA;
}
void SMTLogicBlock::collectVariables() {
}
