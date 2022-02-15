#ifndef LOGICBLOCK_MODEL_H
#define LOGICBLOCK_MODEL_H

#include "Logic.hpp"
namespace logicbase {
class Model {
protected:
  Result result;

public:
  Model() {}
  Model(Result result) : result(result) {}
  virtual ~Model() {}

  Result getResult() { return result; };
  void setResult(Result result) { this->result = result; };

  virtual int getIntValue(const TermInterface &a, LogicBlock *lb) = 0;
  virtual TermInterface getValue(const TermInterface &a, LogicBlock *lb) = 0;
  virtual bool getBoolValue(const TermInterface &a, LogicBlock *lb) = 0;
};
} // namespace logicbase
#endif // LOGICBLOCK_MODEL_H