#ifndef UTIL_LOGIC_H
#define UTIL_LOGIC_H
#include "../Logic.hpp"
#include "../LogicTerm/LogicTermImpl.hpp"
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
  else if (a.getCType() == CType::INT || b.getCType() == CType::INT)
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
inline std::vector<TermInterface> getFlatTerms(const TermInterface &t,
                                               OpType op = OpType::AND) {
  std::vector<TermInterface> terms;
  if (t.getOpType() != op) {
    terms.push_back(t);
  } else {
    for (const TermInterface &it : t.getNodes()) {
      if (it.getOpType() != op) {
        terms.push_back(it);
      } else {
        auto res = getFlatTerms(it, op);
        terms.insert(terms.end(), res.begin(), res.end());
      }
    }
  }
  return terms;
};

inline CType
extractNumberType(const std::vector<TermInterface> &
                      terms) { // TODO check if all terms are numbers, handle BV
  CType res = CType::INT;
  for (const TermInterface &it : terms) {
    if (it.getCType() == CType::REAL) {
      res = CType::REAL;
      break;
    }
  }
  return res;
};

}; // namespace logicutil

#endif // UTIL_LOGIC_H