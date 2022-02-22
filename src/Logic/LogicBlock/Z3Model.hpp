#ifndef LogicTerm_Z3MODEL_H
#define LogicTerm_Z3MODEL_H

#include "Logic.hpp"
#include "Model.hpp"
#include "z3++.h"

namespace z3logic {

using namespace logicbase;

class Z3Model : public Model {
protected:
  z3::model model;
  z3::context &ctx;
  z3::optimize &optimizer;

public:
  Z3Model(z3::context &ctx, z3::optimize &optimizer, z3::model model)
      : model(model), ctx(ctx), optimizer(optimizer) {}
  int getIntValue(const LogicTerm &a, LogicBlock *lb);
  LogicTerm getValue(const LogicTerm &a, LogicBlock *lb);
  bool getBoolValue(const LogicTerm &a, LogicBlock *lb);
  double getRealValue(const LogicTerm &a, LogicBlock *lb);
  unsigned long long getBitvectorValue(const LogicTerm &a, LogicBlock *lb);
};
} // namespace z3logic
#endif // LogicTerm_Z3MODEL_H