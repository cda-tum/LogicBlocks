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
#include <map>
#include <memory>
#include <utility>

using namespace z3;
using namespace logicbase;

class Z3LogicBlock : public LogicBlockOptimizer {
protected:
  z3::context &ctx;
  std::map<unsigned long long, expr> variables;
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
  expr getExprTerm(unsigned long long id);

  context &getContext() { return ctx; }
};

#endif