#include "Z3Model.hpp"
#include "Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"
#include "Z3Logic.hpp"
#include <z3++.h>

namespace z3logic {

LogicTerm Z3Model::getValue(const LogicTerm &a, LogicBlock *lb) {
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
    return LogicTerm(getBitvectorValue(a, lb), 32);
  } else {
    throw std::runtime_error(
        "TermInterface::getValue: not supported for this CType");
  }
}
bool Z3Model::getBoolValue(const LogicTerm &a, LogicBlock *lb) {
  return z3::eq(model.eval(static_cast<Z3LogicBlock *>(lb)->getExprTerm(
                    a.getID(), a.getCType())),
                ctx.bool_val(true));
}
int Z3Model::getIntValue(const LogicTerm &a, LogicBlock *lb) {
  return model
      .eval(
          static_cast<Z3LogicBlock *>(lb)->getExprTerm(a.getID(), a.getCType()))
      .get_numeral_int();
}

double Z3Model::getRealValue(const LogicTerm &a, LogicBlock *lb) {
  return atof(model
                  .eval(static_cast<Z3LogicBlock *>(lb)->getExprTerm(
                      a.getID(), a.getCType()))
                  .get_decimal_string(20)
                  .c_str());
}
unsigned long long Z3Model::getBitvectorValue(const LogicTerm &a,
                                              LogicBlock *lb) {
  return z3::bv2int(model.eval(static_cast<Z3LogicBlock *>(lb)->getExprTerm(
                        a.getID(), a.getCType())),
                    false);
}
} // namespace z3logic