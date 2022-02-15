#ifndef SMTLIBLOGIC_H
#define SMTLIBLOGIC_H

#include "../LogicBlock.hpp"
#include "../LogicTerm/LogicTerm.hpp"
#include <functional>
#include <iostream>
#include <map>
#include <memory>

using namespace logicbase;
class SMTLogicBlock : logicbase::LogicBlock {
protected:
  std::ostream &out;
  void internal_reset() override;

public:
  SMTLogicBlock(bool convertWhenAssert = false, std::ostream &out = std::cout)
      : logicbase::LogicBlock(convertWhenAssert), out(out) {}
  TermInterface makeVariable(const std::string &name,
                             CType type = CType::BOOL) override {
    return LogicTerm(name, type);
  }

  void produceInstance() override;
  Result solve() override;
  void reset() override {
    delete model;
    model = nullptr;
    clauses.clear();
    internal_reset();
    gid = 0;
  };
};

#endif