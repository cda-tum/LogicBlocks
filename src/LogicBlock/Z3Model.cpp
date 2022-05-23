#include "LogicBlock/Z3Model.hpp"

#include "LogicBlock/Z3Logic.hpp"
#include "utils/logging.hpp"

#include <z3++.h>

namespace z3logic {

    LogicTerm Z3Model::getValue(const LogicTerm& a, LogicBlock* lb) {
        if (a.getOpType() != OpType::Variable) {
            throw std::runtime_error("TermInterface::getValue: not a variable");
        }
        if (a.getCType() == CType::BOOL) {
            return LogicTerm(getBoolValue(a, lb));
        } else if (a.getCType() == CType::INT) {
            return LogicTerm(getIntValue(a, lb));
        } else if (a.getCType() == CType::REAL) {
            return LogicTerm(getRealValue(a, lb));
        } else if (a.getCType() == CType::BITVECTOR) {
            return {getBitvectorValue(a, lb), a.getBitVectorSize()};
        } else {
            throw std::runtime_error(
                    "TermInterface::getValue: not supported for this CType");
        }
    }
    bool Z3Model::getBoolValue(const LogicTerm& a, LogicBlock* lb) {
        auto llb = dynamic_cast<Z3Base*>(lb);
        return z3::eq(model.eval(Z3Base::getExprTerm(a.getID(), a.getCType(), llb)), ctx.bool_val(true));
    }

    int Z3Model::getIntValue(const LogicTerm& a, LogicBlock* lb) {
        auto llb = dynamic_cast<Z3Base*>(lb);
        return static_cast<int>(model.eval(Z3Base::getExprTerm(a.getID(), a.getCType(), llb)).as_int64());
    }

    double Z3Model::getRealValue(const LogicTerm& a, LogicBlock* lb) {
        auto llb = dynamic_cast<Z3Base*>(lb);
        return std::stod(model.eval(Z3Base::getExprTerm(a.getID(), a.getCType(), llb)).get_decimal_string(20));
    }

    unsigned long long Z3Model::getBitvectorValue(const LogicTerm& a, LogicBlock* lb) {
        auto llb = dynamic_cast<Z3Base*>(lb);
        return static_cast<unsigned long long>(model.eval(Z3Base::getExprTerm(a.getID(), a.getCType(), llb)).as_int64());
    }
} // namespace z3logic
