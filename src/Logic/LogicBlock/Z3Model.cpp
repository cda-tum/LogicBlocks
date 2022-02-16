#include "Z3Model.hpp"
#include "Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"
#include "Z3Logic.hpp"

namespace z3logic {

TermInterface Z3Model::getValue(const TermInterface &a, LogicBlock *lb) {
  if (a.getOpType() != OpType::Variable) {
    throw std::runtime_error("TermInterface::getValue: not a variable");
  }
  if (a.getCType() == CType::BOOL) {
    return LogicTerm(getBoolValue(a, lb));
  } else if (a.getCType() == CType::INT) {
    return LogicTerm(getIntValue(a, lb));
  } else {
    throw std::runtime_error(
        "TermInterface::getValue: not supported for this CType");
  }
}
bool Z3Model::getBoolValue(const TermInterface &a, LogicBlock *lb) {
  return z3::eq(model.eval(static_cast<Z3LogicBlock *>(lb)->getExprTerm(
                    a.getID(), a.getCType())),
                ctx.bool_val(true));
}
int Z3Model::getIntValue(const TermInterface &a, LogicBlock *lb) {
  return model
      .eval(
          static_cast<Z3LogicBlock *>(lb)->getExprTerm(a.getID(), a.getCType()))
      .get_numeral_int();
}
} // namespace z3logic