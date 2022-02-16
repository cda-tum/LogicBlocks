#ifndef TermInterface_Z3MODEL_H
#define TermInterface_Z3MODEL_H

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
  int getIntValue(const TermInterface &a, LogicBlock *lb);
  TermInterface getValue(const TermInterface &a, LogicBlock *lb);
  bool getBoolValue(const TermInterface &a, LogicBlock *lb);
};
} // namespace z3logic
#endif // TermInterface_Z3MODEL_H