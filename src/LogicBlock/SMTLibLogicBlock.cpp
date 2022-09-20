#include "LogicBlock/SMTLibLogicBlock.hpp"

#include "LogicUtil/util_logic.hpp"

void SMTLogicBlock::produceInstance() {
    for (const auto& clause: clauses) {
        collectVariables(clause);
    }
    out << "; Generated by LogicBlock" << std::endl;
    out << "(set-option :produce-models true)" << std::endl;
    if (outputLogic != SMTLibLogic::NONE) {
        out << writeLogicDefinition(outputLogic) << std::endl;
    }
    for (const auto& entry: constants) {
        out << writeConstantDefinition(entry.second) << std::endl;
    }

    for (const auto& clause: clauses) {
        out << convert(clause) << std::endl;
    }

    out << "(check-sat)" << std::endl;
    out << "(get-model)" << std::endl;
    out << "(exit)" << std::endl;
}

Result SMTLogicBlock::solve() {
    return Result::SAT;
}

void SMTLogicBlock::internalReset() {
    delete model;
    model = nullptr;
}

SMTLibLogic SMTLogicBlock::getLogicForTerm(const LogicTerm& a) {
    using namespace logicutil;
    switch (a.getOpType()) {
        case OpType::Variable:
        case OpType::Constant:
            switch (a.getCType()) { //Get the smallest possible logic for the term
                case CType::BOOL:
                    return SMTLibLogic::QF_UF;
                case CType::INT:
                    return SMTLibLogic::QF_IDL;
                case CType::REAL:
                    return SMTLibLogic::QF_RDL;
                case CType::BITVECTOR:
                    return SMTLibLogic::QF_BV;
                default:
                    throw std::runtime_error("Unsupported CType");
            }
            break;
        case OpType::NEG: {
            return getMinimumLogic(SMTLibLogic::QF_UF, getLogicForTerm(a.getNodes()[0]));
        }
        case OpType::AND:
        case OpType::OR: {
            SMTLibLogic logic = SMTLibLogic::QF_UF;
            for (const auto& node: a.getNodes()) {
                logic = getMinimumLogic(logic, getLogicForTerm(node));
            }
            return logic;
        }
        case OpType::IMPL:
        case OpType::XOR:
        case OpType::EQ: {
            return getMinimumLogic(getMinimumLogic(SMTLibLogic::QF_UF, getLogicForTerm(a.getNodes()[0])), getLogicForTerm(a.getNodes()[1]));
        }
        case OpType::ITE: {
            return getMinimumLogic(getMinimumLogic(getMinimumLogic(SMTLibLogic::QF_UF, getLogicForTerm(a.getNodes()[0])), getLogicForTerm(a.getNodes()[1])), getLogicForTerm(a.getNodes()[2]));
        }
        case OpType::ADD:
        case OpType::SUB:
        case OpType::MUL: {
            SMTLibLogic logic = SMTLibLogic::QF_LRA;
            for (const auto& node: a.getNodes()) {
                logic = getMinimumLogic(logic, getLogicForTerm(node));
            }
            return logic;
        }
        case OpType::DIV:

        default:
            return SMTLibLogic::QF_UFNRA;
    }
    return SMTLibLogic::QF_UFNRA;
}
void SMTLogicBlock::collectVariables(const LogicTerm& a) {
    switch (a.getOpType()) {
        case OpType::Variable:
            constants.insert_or_assign(a.getID(), a);
            break;
        case OpType::Constant:
            break;
        default:
            for (const auto& subnode: a.getNodes()) {
                collectVariables(subnode);
            }
    }
}

std::string SMTLogicBlock::getConstantString(const LogicTerm& a) {
    return a.getName() + "_" + std::to_string(a.getID());
}

std::string SMTLogicBlock::writeConstantDefinition(const LogicTerm& a) {
    return "(declare-const " + getConstantString(a) + " " + getTypeString(a) + ")";
}

std::string SMTLogicBlock::getTypeString(const LogicTerm& a) {
    switch (a.getCType()) {
        case CType::BOOL:
            return "Bool";
        case CType::INT:
            return "Int";
        case CType::REAL:
            return "Real";
        case CType::BITVECTOR:
            return "(_ BitVec " + std::to_string(a.getBitVectorSize()) + ")";
        default:
            throw std::runtime_error("Unsupported CType" + std::to_string(static_cast<int>(a.getCType())));
    }
}

SMTLibLogic SMTLogicBlock::getMinimumLogic(const SMTLibLogic& a, const SMTLibLogic& b) {
    bool needsUF    = a == SMTLibLogic::QF_UFNRA || b == SMTLibLogic::QF_UFNRA || a == SMTLibLogic::QF_UFNIA || b == SMTLibLogic::QF_UFNIA || a == SMTLibLogic::QF_UF || b == SMTLibLogic::QF_UF || a == SMTLibLogic::QF_UFLIA || b == SMTLibLogic::QF_UFLIA || a == SMTLibLogic::QF_UFLRA || b == SMTLibLogic::QF_UFLRA || a == SMTLibLogic::QF_UFBV || b == SMTLibLogic::QF_UFBV || a == SMTLibLogic::QF_UFIDL || b == SMTLibLogic::QF_UFIDL || a == SMTLibLogic::QF_UFRDL || b == SMTLibLogic::QF_UFRDL;
    bool needsR     = a == SMTLibLogic::QF_UFNRA || b == SMTLibLogic::QF_UFNRA || a == SMTLibLogic::QF_NRA || b == SMTLibLogic::QF_NRA || a == SMTLibLogic::QF_LRA || b == SMTLibLogic::QF_LRA || a == SMTLibLogic::QF_RDL || b == SMTLibLogic::QF_RDL || a == SMTLibLogic::QF_UFLRA || b == SMTLibLogic::QF_UFLRA || a == SMTLibLogic::QF_UFRDL || b == SMTLibLogic::QF_UFRDL;
    bool needsI     = a == SMTLibLogic::QF_UFNIA || b == SMTLibLogic::QF_UFNIA || a == SMTLibLogic::QF_NIA || b == SMTLibLogic::QF_NIA || a == SMTLibLogic::QF_LIA || b == SMTLibLogic::QF_LIA || a == SMTLibLogic::QF_IDL || b == SMTLibLogic::QF_IDL || a == SMTLibLogic::QF_UFLIA || b == SMTLibLogic::QF_UFLIA || a == SMTLibLogic::QF_UFIDL || b == SMTLibLogic::QF_UFIDL;
    bool needsBV    = a == SMTLibLogic::QF_UFBV || b == SMTLibLogic::QF_UFBV || a == SMTLibLogic::QF_BV || b == SMTLibLogic::QF_BV;
    bool needsArith = a == SMTLibLogic::QF_UFNRA || b == SMTLibLogic::QF_UFNRA || a == SMTLibLogic::QF_UFNIA || b == SMTLibLogic::QF_UFNIA || a == SMTLibLogic::QF_NRA || b == SMTLibLogic::QF_NRA || a == SMTLibLogic::QF_NIA || b == SMTLibLogic::QF_NIA || a == SMTLibLogic::QF_LRA || b == SMTLibLogic::QF_LRA || a == SMTLibLogic::QF_LIA || b == SMTLibLogic::QF_LIA || a == SMTLibLogic::QF_UFLRA || b == SMTLibLogic::QF_UFLRA || a == SMTLibLogic::QF_UFLIA || b == SMTLibLogic::QF_UFLIA;
    bool needsN     = a == SMTLibLogic::QF_UFNRA || b == SMTLibLogic::QF_UFNRA || a == SMTLibLogic::QF_UFNIA || b == SMTLibLogic::QF_UFNIA || a == SMTLibLogic::QF_NRA || b == SMTLibLogic::QF_NRA || a == SMTLibLogic::QF_NIA || b == SMTLibLogic::QF_NIA;
    if (needsUF) {     //Needing UF
        if (needsBV) { //Needing BV
            if (needsArith || needsR || needsI) {
                throw std::runtime_error("Unsupported Logic Combination");
            }
            {
                return SMTLibLogic::QF_UFBV;
            }
        } else if (needsN) { //Needing Nonlinearity implies also needing Arithmetic
            if (needsR && needsI) {
                return SMTLibLogic::QF_UFNRA;
            } else if (needsR) {
                return SMTLibLogic::QF_UFNRA;
            } else if (needsI) {
                return SMTLibLogic::QF_UFNIA;
            } else {
                throw std::runtime_error("Unsupported Logic Combination");
            }
        } else if (needsArith) { //Arithmetic without Nonlinearity
            if (needsR && needsI) {
                return SMTLibLogic::QF_UFLRA;
            } else if (needsR) {
                return SMTLibLogic::QF_UFLRA;
            } else if (needsI) {
                return SMTLibLogic::QF_UFLIA;
            } else {
                throw std::runtime_error("Unsupported Logic Combination");
            }
        } else if (needsR) { //Reals without Arithmetic
            return SMTLibLogic::QF_UFRDL;
        } else if (needsI) { //Integers without Arithmetic
            return SMTLibLogic::QF_UFIDL;
        } else { //Only UF
            return SMTLibLogic::QF_UF;
        }
    } else {
        if (needsBV) { //Needing BV
            if (needsArith || needsR || needsI) {
                throw std::runtime_error("Unsupported Logic Combination");
            }
            {
                return SMTLibLogic::QF_BV;
            }
        } else if (needsN) { //Needing Nonlinearity implies also needing Arithmetic
            if (needsR && needsI) {
                return SMTLibLogic::QF_NRA;
            } else if (needsR) {
                return SMTLibLogic::QF_NRA;
            } else if (needsI) {
                return SMTLibLogic::QF_NIA;
            } else {
                throw std::runtime_error("Unsupported Logic Combination");
            }
        } else if (needsArith) { //Arithmetic without Nonlinearity
            if (needsR && needsI) {
                return SMTLibLogic::QF_LRA;
            } else if (needsR) {
                return SMTLibLogic::QF_LRA;
            } else if (needsI) {
                return SMTLibLogic::QF_LIA;
            } else {
                throw std::runtime_error("Unsupported Logic Combination");
            }
        } else if (needsR) { //Reals without Arithmetic
            return SMTLibLogic::QF_RDL;
        } else if (needsI) { //Integers without Arithmetic
            return SMTLibLogic::QF_IDL;
        } else { //Only UF
            throw std::runtime_error("Unsupported Logic Combination");
        }
    }
    return SMTLibLogic::QF_LIA;
}
std::string SMTLogicBlock::writeLogicDefinition(const SMTLibLogic& logic) {
    switch (logic) {
        case SMTLibLogic::QF_UF:
            return "(set-logic QF_UF)";
        case SMTLibLogic::QF_UFNRA:
            return "(set-logic QF_UFNRA)";
        case SMTLibLogic::QF_UFNIA:
            return "(set-logic QF_UFNIA)";
        case SMTLibLogic::QF_UFRDL:
            return "(set-logic QF_UFRDL)";
        case SMTLibLogic::QF_UFIDL:
            return "(set-logic QF_UFIDL)";
        case SMTLibLogic::QF_UFBV:
            return "(set-logic QF_UFBV)";
        case SMTLibLogic::QF_UFLRA:
            return "(set-logic QF_UFLRA)";
        case SMTLibLogic::QF_UFLIA:
            return "(set-logic QF_UFLIA)";
        case SMTLibLogic::QF_NRA:
            return "(set-logic QF_NRA)";
        case SMTLibLogic::QF_NIA:
            return "(set-logic QF_NIA)";
        case SMTLibLogic::QF_RDL:
            return "(set-logic QF_RDL)";
        case SMTLibLogic::QF_IDL:
            return "(set-logic QF_IDL)";
        case SMTLibLogic::QF_BV:
            return "(set-logic QF_BV)";
        case SMTLibLogic::QF_LRA:
            return "(set-logic QF_LRA)";
        case SMTLibLogic::QF_LIA:
            return "(set-logic QF_LIA)";

        case SMTLibLogic::NONE: break;
    }
    return "";
}
std::string SMTLogicBlock::convert(const LogicTerm& term) {
    switch (term.getOpType()) {
        case OpType::Constant:
            return term.getConstantValue();
        case OpType::Variable:
            return getConstantString(term);
        case OpType::EQ:
            return "(= " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::XOR:
            return "(xor " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::OR:
            return "(or " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::AND:
            return "(and " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::NEG:
            return "(not " + convert(term.getNodes()[0]) + ")";
        case OpType::ITE:
            return "(ite " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + " " + convert(term.getNodes()[2]) + ")";
        case OpType::IMPL:
            return "(=> " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::ADD:
            return "(+ " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::SUB:
            return "(- " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::MUL:
            return "(* " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::DIV:
            return "(div " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::LT:
            return "(< " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::LTE:
            return "(<= " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::GT:
            return "(> " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::GTE:
            return "(>= " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::BitAnd:
            return "(bvand " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::BitOr:
            return "(bvor " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::BitXor:
            return "(bvxor " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::BitEq:
            return "(= " + convert(term.getNodes()[0]) + " " + convert(term.getNodes()[1]) + ")";
        case OpType::None: break;
        case OpType::CALL: break;
        case OpType::GET: break;
        case OpType::SET: break;
    }
    return "";
}
void SMTLogicBlock::assertFormula(const LogicTerm& a) {
    clauses.insert(a);
}
