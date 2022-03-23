#ifndef LOGICBLOCK_LOGIC_H
#define LOGICBLOCK_LOGIC_H

#include <cassert>
#include <functional>
#include <memory>
#include <ostream>
#include <sstream>
#include <cstdarg>
#include <stdexcept>
#include <string>
#include <vector>

namespace logicbase {
enum class Result { SAT, UNSAT, NDEF };
enum class OpType {
  None,
  Constant,
  Variable,
  EQ,
  XOR,
  AND,
  OR,
  ITE,
  NEG,
  IMPL,
  ADD,
  SUB,
  MUL,
  DIV,
  GT,
  LT,
  CALL,
  GET,
  SET,
  BIT_AND,
  BIT_OR,
  BIT_EQ,
  BIT_XOR
};

enum class TermType { BASE, CNF };

enum class CType {
  BOOL,
  INT,
  REAL,
  BITVECTOR,
  FUNCTION,
  ARRAY,
  SET,
  ERRORTYPE
};

inline std::string toString(CType ctype) {
  switch (ctype) {
  case CType::BOOL:
    return "B";
  case CType::BITVECTOR:
    return "BV";
  case CType::INT:
    return "I";
  case CType::REAL:
    return "F";
  case CType::FUNCTION:
    return "F(...)";
  case CType::ARRAY:
    return "A[...]";
  case CType::SET:
    return "S(...)";
  case CType::ERRORTYPE:
    throw std::runtime_error("Error: Unknown CType");
  }
  return "Error";
}
inline CType CTypeFromString(std::string ctype) {
  if (ctype == "B")
    return CType::BOOL;
  if (ctype == "BV")
    return CType::BITVECTOR;
  if (ctype == "I")
    return CType::INT;
  if (ctype == "F")
    return CType::REAL;
  if (ctype == "F(...)")
    return CType::FUNCTION;
  if (ctype == "A[...]")
    return CType::ARRAY;
  if (ctype == "S(...)")
    return CType::SET;
  return CType::BOOL;
}

inline bool isArith(OpType optype) {
  switch (optype) {
  case OpType::ADD:
  case OpType::SUB:
  case OpType::MUL:
  case OpType::DIV:
  case OpType::GT:
  case OpType::LT:
    return true;
  default:
    return false;
  }
}

inline bool isNumber(CType ctype) {
  switch (ctype) {
  case CType::INT:
  case CType::REAL:
  case CType::BITVECTOR:
    return true;
  default:
    return false;
  }
}

inline bool isCommutative(OpType op) {
  switch (op) {
  case OpType::ADD:
  case OpType::MUL:
  case OpType::EQ:
  case OpType::XOR:
  case OpType::AND:
  case OpType::OR:
    return true;
  default:
    return false;
  }
}

inline bool isAssociative(OpType op) {
  switch (op) {
  case OpType::ADD:
  case OpType::MUL:
  case OpType::EQ:
  case OpType::XOR:
  case OpType::AND:
  case OpType::OR:
    return true;
  default:
    return false;
  }
}
inline bool hasNeutralElement(OpType op) {
  switch (op) {
  case OpType::ADD:
  case OpType::MUL:
  case OpType::AND:
  case OpType::OR:
    return true;
  default:
    return false;
  }
}

inline CType getCType(OpType op) {
  switch (op) {
  case OpType::NEG:
  case OpType::IMPL:
  case OpType::AND:
  case OpType::OR:
    return CType::BOOL;
  case OpType::ADD:
  case OpType::SUB:
  case OpType::MUL:
  case OpType::DIV:
  case OpType::GT:
  case OpType::LT:
    return CType::INT;
  case OpType::ITE:
    return CType::BOOL;
  case OpType::BIT_AND:
  case OpType::BIT_OR:
  case OpType::BIT_EQ:
  case OpType::BIT_XOR:
    return CType::BITVECTOR;
  default:
    return CType::BOOL;
  }
}

class TermImpl;
class LogicTermImpl;
class LogicTerm;

using LogicVector = std::vector<LogicTerm>;
using LogicMatrix = std::vector<LogicVector>;
using LogicMatrix3D = std::vector<LogicMatrix>;

class Logic {
public:
  virtual unsigned long long getNextId() = 0;
  virtual unsigned long long getId() = 0;
};

class TermInterface {
public:
  virtual ~TermInterface() = default;
  virtual long long getID() const = 0;
  virtual const std::vector<LogicTerm> &getNodes() const = 0;
  virtual OpType getOpType() const = 0;
  virtual CType getCType() const = 0;
  virtual bool getBoolValue() const = 0;
  virtual int getIntValue() const = 0;
  virtual double getFloatValue() const = 0;
  virtual unsigned long long getBitVectorValue() const = 0;
  virtual short getBitVectorSize() const = 0;
  virtual const std::string &getName() const = 0;
  virtual Logic *getLogic() const = 0;
  virtual std::shared_ptr<TermImpl> getImplementation() const = 0;
  virtual bool deepEquals(const LogicTerm &other) const = 0;
  virtual void print(std::ostream &os) const = 0;
  virtual unsigned long long getDepth() const = 0;
  virtual unsigned long long getMaxChildrenDepth() const = 0;
};

struct TermHash {
  std::size_t operator()(const TermInterface &t) const {
    if (t.getOpType() == OpType::None) {
      throw std::runtime_error("Invalid OpType");
    }
    return t.getID();
  }
  bool operator()(const TermInterface &t1, const TermInterface &t2) const {
    if (t1.getOpType() == OpType::None || t2.getOpType() == OpType::None) {
      throw std::runtime_error("Invalid OpType");
    }
    if (t1.getOpType() == OpType::Constant &&
        t2.getOpType() == OpType::Constant && t1.getCType() == t2.getCType()) {
      switch (t1.getCType()) {
      case CType::BOOL:
        return t1.getBoolValue() == t2.getBoolValue();
      case CType::INT:
        return t1.getIntValue() == t2.getIntValue();
      case CType::REAL:
        return t1.getFloatValue() == t2.getFloatValue();
      default:
        return false;
      }
    } else {
      return t1.getID() == t2.getID();
    }
  }
};
struct TermDepthComparator {
  bool operator()(const TermInterface &t1, const TermInterface &t2) const {
    if (t1.getOpType() == OpType::None || t2.getOpType() == OpType::None) {
      throw std::runtime_error("Invalid OpType");
    }
    if ((t1.getOpType() == OpType::Variable &&
         t2.getOpType() == OpType::Variable) ||
        (t1.getOpType() == OpType::Constant &&
         t2.getOpType() == OpType::Constant) ||
        t1.getDepth() == t2.getDepth()) {
      return t1.getID() > t2.getID();
    } else {
      return t1.getDepth() > t2.getDepth();
    }
  }
};

class LogicBlock;
class Model;

} // namespace logicbase
#endif // LOGICBLOCK_LOGIC_H