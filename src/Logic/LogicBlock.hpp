#ifndef LOGICBLOCK_H
#define LOGICBLOCK_H

#include "Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"
#include "Model.hpp"
#include <set>
#include <sys/types.h>
#include <vector>

namespace logicbase {
class LogicBlock : public Logic {
protected:
  std::set<LogicTerm, TermDepthComparator> clauses;
  Model *model{};
  bool convertWhenAssert;
  virtual void internal_reset() = 0;
  unsigned long long gid = 0;

public:
  LogicBlock(bool convertWhenAssert = false)
      : convertWhenAssert(convertWhenAssert) {}
  virtual ~LogicBlock() {}

  unsigned long long getNextId() { return gid++; };
  unsigned long long getId() { return gid; };

  Model *getModel() { return model; }

  void dump(const TermInterface &a, std::ostream &stream) { a.print(stream); }
  void dumpAll(std::ostream &stream) {
    for (const TermInterface &term : clauses) {
      dump(term, stream);
      stream << std::endl;
    }
  }

  void assertFormula(const LogicTerm &a) {
    if (a.getOpType() == OpType::AND) {
      for (const auto &clause : a.getNodes()) {
        clauses.insert(clause);
      }
    } else {
      clauses.insert(a);
    }
  }

  virtual LogicTerm makeVariable(const std::string &name,
                                 CType type = CType::BOOL) = 0;

  virtual void produceInstance() = 0;
  virtual Result solve() = 0;
  virtual void reset() {
    delete model;
    model = nullptr;
    clauses.clear();
    internal_reset();
    gid = 0;
  };
};

class LogicBlockOptimizer : public LogicBlock {
protected:
  std::vector<std::pair<LogicTerm, double>> weightedTerms;
  virtual void internal_reset() = 0;

public:
  LogicBlockOptimizer(bool convertWhenAssert) : LogicBlock(convertWhenAssert) {}
  virtual ~LogicBlockOptimizer() {}
  void weightedTerm(const LogicTerm &a, double weight) {
    weightedTerms.push_back(std::make_pair(a, weight));
  };
  virtual bool makeMinimize() = 0;
  virtual bool makeMaximize() = 0;
  virtual bool maximize(const LogicTerm &term) = 0;
  virtual bool minimize(const LogicTerm &term) = 0;
  virtual void reset() {
    model = nullptr;
    clauses.clear();
    weightedTerms.clear();
    internal_reset();
    gid = 0;
  };
};
} // namespace logicbase
#endif // LOGICBLOCK_H