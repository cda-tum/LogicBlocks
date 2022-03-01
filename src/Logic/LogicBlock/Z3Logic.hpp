//
// Created by Sarah on 08.07.2021.
//

#ifndef CLIFFORDSATOPT_Z3LOGIC_H
#define CLIFFORDSATOPT_Z3LOGIC_H
#include "../Logic.hpp"
#include "../LogicBlock.hpp"
#include "Z3Model.hpp"
#include "utils/util.hpp"
#include "z3++.h"
#include <functional>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include <z3++.h>
#include <z3_api.h>

namespace z3logic {

using namespace z3;
using namespace logicbase;

class Z3LogicBlock : public LogicBlockOptimizer {
protected:
  z3::context internal_ctx{};
  z3::optimize internal_optimizer{internal_ctx};
  z3::context &ctx;
  std::map<unsigned long long, std::vector<std::pair<bool, expr>>> variables;
  optimize &optimizer;
  void internal_reset() override;

  std::unordered_map<LogicTerm, std::vector<std::pair<bool, expr>>, TermHash,
                     TermHash>
      cache{};

public:
  Z3LogicBlock(context &ctx, optimize &optimizer, bool convertWhenAssert = true)
      : LogicBlockOptimizer(convertWhenAssert), ctx(ctx), optimizer(optimizer) {
  }
  Z3LogicBlock(bool convertWhenAssert = true)
      : LogicBlockOptimizer(convertWhenAssert), ctx(internal_ctx),
        optimizer(internal_optimizer) {}
  ~Z3LogicBlock() { internal_reset(); }
  void assertFormula(const LogicTerm &a) override;
  bool makeMinimize() override;
  bool makeMaximize() override;
  bool maximize(const LogicTerm &term) override;
  bool minimize(const LogicTerm &term) override;
  void produceInstance() override;
  Result solve() override;

  void setOptimizer(optimize &Optimizer);
  optimize &getOptimizer();
  expr convert(const LogicTerm &a, CType to_type = CType::BOOL);
  expr getExprTerm(unsigned long long id, CType type);

  void dumpZ3State(std::ostream &stream);

  context &getContext() { return ctx; }
  z3::expr convertVariableTo(const LogicTerm &a, CType to_type);
  z3::expr convertVariableFromBoolTo(const LogicTerm &a, CType to_type);
  z3::expr convertVariableFromIntTo(const LogicTerm &a, CType to_type);
  z3::expr convertVariableFromRealTo(const LogicTerm &a, CType to_type);
  z3::expr convertVariableFromBitvectorTo(const LogicTerm &a, CType to_type);

  z3::expr convertOperator(const LogicTerm &a, const LogicTerm &b,
                           z3::expr (*op)(const z3::expr &, const z3::expr &),
                           CType to_type);
  z3::expr convertOperator(const LogicTerm &a, z3::expr (*op)(const z3::expr &),
                           CType to_type);
  z3::expr convertOperator(const LogicTerm &a, const LogicTerm &b,
                           const LogicTerm &c,
                           z3::expr (*op)(const z3::expr &, const z3::expr &,
                                          const z3::expr &),
                           CType to_type);
  z3::expr convertOperator(std::vector<LogicTerm> terms,
                           z3::expr (*op)(const z3::expr &, const z3::expr &),
                           CType to_type);

  z3::expr convertConstant(const LogicTerm &a, CType to_type);
};

} // namespace z3logic
#endif // CLIFFORDSATOPT_Z3LOGIC_H