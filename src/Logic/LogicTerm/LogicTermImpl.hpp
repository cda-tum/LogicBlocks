#ifndef LogicTermImpl_HPP
#define LogicTermImpl_HPP
#include "../Logic.hpp"
#include "TermImpl.hpp"
#include <cmath>
#include <map>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace logicbase {
class LogicTermImpl : public TermImpl {

public:
  explicit LogicTermImpl(bool v) : TermImpl(v) {}
  explicit LogicTermImpl(int v) : TermImpl(v) {}
  explicit LogicTermImpl(double v) : TermImpl(v) {}
  explicit LogicTermImpl(unsigned long long v, short bv_size)
      : TermImpl(v, bv_size) {}
  explicit LogicTermImpl(const char *name, CType cType = CType::BOOL,
                         Logic *lb = nullptr)
      : TermImpl(name, cType, lb) {}
  explicit LogicTermImpl(OpType opType, const std::string name,
                         CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(opType, name, cType, lb) {}
  explicit LogicTermImpl(CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(cType, lb) {}
  explicit LogicTermImpl(OpType ot, const TermInterface &a,
                         const TermInterface &b, CType cType = CType::BOOL,
                         Logic *lb = nullptr)
      : TermImpl(ot, {a, b}, cType, lb) {}
  explicit LogicTermImpl(OpType ot, const TermInterface &a,
                         const TermInterface &b, const TermInterface &c,
                         CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(ot, {a, b, c}, cType, lb) {}
  explicit LogicTermImpl(OpType ot, const TermInterface &a,
                         CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(ot, {a}, cType, lb) {}
  explicit LogicTermImpl(OpType ot,
                         const std::initializer_list<TermInterface> &n,
                         CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(ot, n, cType, lb) {}
  explicit LogicTermImpl(OpType ot, const std::vector<TermInterface> &n,
                         CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(ot, n, cType, lb) {}
};
}; // namespace logicbase

#endif // LogicTermImpl_HPP