#ifndef UTIL_LOGIC_H
#define UTIL_LOGIC_H

#include "LogicTerm/LogicTerm.hpp"

#include <memory>
#include <stdexcept>
#include <vector>

namespace logicutil {
    using namespace logicbase;
    inline bool isConst(const LogicTerm& a) {
        return a.getOpType() == OpType::Constant;
    }
    inline bool isVar(const LogicTerm& a) {
        return a.getOpType() == OpType::Variable;
    }

    inline bool isUnit(const LogicTerm& a) {
        return isConst(a) || isVar(a) || (a.getOpType() == OpType::NEG && a.getNodes()[0].getOpType() == OpType::Constant) || (a.getOpType() == OpType::NEG && a.getNodes()[0].getOpType() == OpType::Variable);
    }

    inline CType getTargetCType(const LogicTerm& a, const LogicTerm& b, OpType op) {
        if (op == OpType::EQ || op == OpType::XOR || op == OpType::AND ||
            op == OpType::OR || op == OpType::GT || op == OpType::LT || op == OpType::GTE || op == OpType::LTE) {
            return CType::BOOL;
        }
        if (a.getCType() == CType::REAL || b.getCType() == CType::REAL) {
            return CType::REAL;
        }
        if (a.getCType() == CType::BITVECTOR || b.getCType() == CType::BITVECTOR) {
            return CType::BITVECTOR;
        }
        if (a.getCType() == CType::INT || b.getCType() == CType::INT) {
            return CType::INT;
        }
        return CType::BOOL;
    }
    inline CType getTargetCType(CType targetType, const LogicTerm& b) {
        if (targetType == CType::REAL || b.getCType() == CType::REAL) {
            return CType::REAL;
        }
        if (targetType == CType::BITVECTOR || b.getCType() == CType::BITVECTOR) {
            return CType::BITVECTOR;
        }
        if (targetType == CType::INT || b.getCType() == CType::INT) {
            return CType::INT;
        }
        return CType::BOOL;
    }

    inline Logic* getValidLogicPtr(const LogicTerm& a, const LogicTerm& b) {
        if (isConst(a) || isConst(b)) {
            if (!isConst(a)) {
                return a.getLogic();
            }
            if (!isConst(b)) {
                return b.getLogic();
            }
            return nullptr;
        }
        if (a.getLogic() == b.getLogic()) {
            return a.getLogic();
        }
        throw std::runtime_error("Logic mismatch");
    }
    inline Logic* getValidLogicPtr(const LogicTerm& a, const LogicTerm& b,
                                   const LogicTerm& c) {
        if (isConst(a) || isConst(b) || isConst(c)) {
            if (!isConst(a)) {
                return a.getLogic();
            }
            if (!isConst(b)) {
                return b.getLogic();
            }
            if (!isConst(c)) {
                return c.getLogic();
            }
            return nullptr;
        }
        if (a.getLogic() == b.getLogic() && b.getLogic() == c.getLogic()) {
            return a.getLogic();
        }
        throw std::runtime_error("Logic mismatch");
    }
    inline std::vector<LogicTerm> getFlatTerms(const LogicTerm& t,
                                               OpType           op = OpType::AND) {
        std::vector<LogicTerm> terms;
        if (t.getOpType() != op) {
            terms.push_back(t);
        } else {
            for (const LogicTerm& it: t.getNodes()) {
                if (it.getOpType() != op) {
                    terms.push_back(it);
                } else {
                    auto res = getFlatTerms(it, op);
                    terms.insert(terms.end(), res.begin(), res.end());
                }
            }
        }
        return terms;
    };

    inline CType
    extractNumberType(const std::vector<LogicTerm>&
                              terms) { // TODO check if all terms are numbers, handle BV
        CType res = CType::INT;
        for (const LogicTerm& it: terms) {
            if (it.getCType() == CType::REAL) {
                res = CType::REAL;
                break;
            }
            if (it.getCType() == CType::BITVECTOR) {
                res = CType::BITVECTOR;
                break;
            }
        }
        return res;
    }

} // namespace logicutil

#endif // UTIL_LOGIC_H
