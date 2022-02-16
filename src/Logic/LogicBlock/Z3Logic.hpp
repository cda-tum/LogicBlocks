//
// Created by Sarah on 08.07.2021.
//

#ifndef CLIFFORDSATOPT_Z3LOGIC_H
#define CLIFFORDSATOPT_Z3LOGIC_H
#include "Logic.hpp"
#include "LogicBlock.hpp"
#include "Z3Model.hpp"
#include "utils/util.hpp"
#include "z3++.h"
#include <functional>
#include <initializer_list>
#include <map>
#include <memory>
#include <utility>
#include <z3_api.h>

namespace z3logic {

using namespace z3;
using namespace logicbase;

class Z3LogicBlock : public LogicBlockOptimizer {
protected:
  z3::context &ctx;
  std::map<unsigned long long, std::vector<std::pair<bool, expr>>> variables;
  optimize &optimizer;
  void internal_reset();

  std::unordered_map<TermInterface, std::vector<std::pair<bool, expr>>,
                     TermHash, TermHash>
      cache{};

public:
  Z3LogicBlock(context &ctx, optimize &optimizer, bool convertWhenAssert = true)
      : LogicBlockOptimizer(convertWhenAssert), ctx(ctx), optimizer(optimizer) {
  }
  ~Z3LogicBlock() { internal_reset(); }
  bool makeMinimize();
  bool makeMaximize();
  bool maximize(const TermInterface &term);
  bool minimize(const TermInterface &term);
  void produceInstance();
  Result solve();

  void setOptimizer(optimize &Optimizer);
  optimize &getOptimizer();
  expr convert(const TermInterface &a, CType to_type = CType::BOOL);
  expr getExprTerm(unsigned long long id, CType type);

  context &getContext() { return ctx; }
  z3::expr convertVariableTo(const TermInterface &a, CType to_type);
  z3::expr convertVariableFromBoolTo(const TermInterface &a, CType to_type);
  z3::expr convertVariableFromIntTo(const TermInterface &a, CType to_type);
  z3::expr convertVariableFromRealTo(const TermInterface &a, CType to_type);
  z3::expr convertVariableFromBitvectorTo(const TermInterface &a,
                                          CType to_type);

  z3::expr convertOperator(const TermInterface &a, const TermInterface &b,
                           z3::expr (*op)(const z3::expr &, const z3::expr &),
                           CType to_type);
  z3::expr convertOperator(const TermInterface &a,
                           z3::expr (*op)(const z3::expr &), CType to_type);
  z3::expr convertOperator(const TermInterface &a, const TermInterface &b,
                           const TermInterface &c,
                           z3::expr (*op)(const z3::expr &, const z3::expr &,
                                          const z3::expr &),
                           CType to_type);
  z3::expr convertOperator(std::vector<TermInterface> terms,
                           z3::expr (*op)(const z3::expr &, const z3::expr &),
                           CType to_type);
};

} // namespace z3logic
#endif // CLIFFORDSATOPT_Z3LOGIC_H