#ifndef UTIL_LOGIC_H
#define UTIL_LOGIC_H
#include "../Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"
#include <memory>
#include <stdexcept>
#include <vector>

namespace logicutil {
using namespace logicbase;
inline bool isConst(const TermInterface &a) {
  return a.getOpType() == OpType::Constant;
}
inline bool isVar(const TermInterface &a) {
  return a.getOpType() == OpType::Variable;
}
inline CType getTargetCType(const TermInterface &a, const TermInterface &b) {
  if (a.getCType() == CType::REAL || b.getCType() == CType::REAL)
    return CType::REAL;
  else if (a.getCType() == CType::BITVECTOR || b.getCType() == CType::BITVECTOR)
    return CType::BITVECTOR;
  else if (a.getCType() == CType::INT || b.getCType() == CType::INT)
    return CType::INT;
  else
    return CType::BOOL;
}
inline CType getTargetCType(CType targetType, const TermInterface &b) {
  if (targetType == CType::REAL || b.getCType() == CType::REAL)
    return CType::REAL;
  else if (targetType == CType::BITVECTOR || b.getCType() == CType::BITVECTOR)
    return CType::BITVECTOR;
  else if (targetType == CType::INT || b.getCType() == CType::INT)
    return CType::INT;
  else
    return CType::BOOL;
}

inline Logic *getValidLogic_ptr(const TermInterface &a,
                                const TermInterface &b) {
  if (isConst(a) || isConst(b)) {
    if (!isConst(a))
      return a.getLogic();
    else if (!isConst(b))
      return b.getLogic();
    else
      return nullptr;
  } else {
    if (a.getLogic() == b.getLogic())
      return a.getLogic();
    else
      throw std::runtime_error("Logic mismatch");
  }
}
inline Logic *getValidLogic_ptr(const TermInterface &a, const TermInterface &b,
                                const TermInterface &c) {
  if (isConst(a) || isConst(b) || isConst(c)) {
    if (!isConst(a))
      return a.getLogic();
    else if (!isConst(b))
      return b.getLogic();
    else if (!isConst(c))
      return c.getLogic();
    else
      return nullptr;
  } else {
    if (a.getLogic() == b.getLogic() && b.getLogic() == c.getLogic())
      return a.getLogic();
    else
      throw std::runtime_error("Logic mismatch");
  }
}
inline std::vector<LogicTerm> getFlatTerms(const TermInterface &t,
                                           OpType op = OpType::AND) {
  std::vector<LogicTerm> terms;
  if (t.getOpType() != op) {
    terms.push_back(LogicTerm(t));
  } else {
    for (const TermInterface &it : t.getNodes()) {
      if (it.getOpType() != op) {
        terms.push_back(LogicTerm(it));
      } else {
        auto res = getFlatTerms(it, op);
        terms.insert(terms.end(), res.begin(), res.end());
      }
    }
  }
  return terms;
};

inline CType
extractNumberType(const std::vector<LogicTerm> &
                      terms) { // TODO check if all terms are numbers, handle BV
  CType res = CType::INT;
  for (const LogicTerm &it : terms) {
    if (it.getCType() == CType::REAL) {
      res = CType::REAL;
      break;
    } else if (it.getCType() == CType::BITVECTOR) {
      res = CType::BITVECTOR;
      break;
    }
  }
  return res;
};

}; // namespace logicutil

#endif // UTIL_LOGIC_H