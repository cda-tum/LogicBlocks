#ifndef LogicTermImpl_HPP
#define LogicTermImpl_HPP
#include "../Logic.hpp"
#include "LogicTerm.hpp"
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
  explicit LogicTermImpl(OpType ot, const LogicTerm &a, const LogicTerm &b,
                         CType cType = CType::BOOL, Logic *lb = nullptr) {
    opType = ot;
    c_type = cType;
    this->lb = lb;
    nodes.push_back(a);
    nodes.push_back(b);
  }
  explicit LogicTermImpl(OpType ot, const LogicTerm &a, const LogicTerm &b,
                         const LogicTerm &c, CType cType = CType::BOOL,
                         Logic *lb = nullptr) {
    opType = ot;
    c_type = cType;
    this->lb = lb;
    nodes.push_back(a);
    nodes.push_back(b);
    nodes.push_back(c);
  }
  explicit LogicTermImpl(OpType ot, const LogicTerm &a,
                         CType cType = CType::BOOL, Logic *lb = nullptr) {
    opType = ot;
    c_type = cType;
    this->lb = lb;
    nodes.push_back(a);
  }
  explicit LogicTermImpl(OpType ot,
                         const std::initializer_list<TermInterface> &n,
                         CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(ot, n, cType, lb) {}
  explicit LogicTermImpl(OpType ot, const std::vector<TermInterface> &n,
                         CType cType = CType::BOOL, Logic *lb = nullptr)
      : TermImpl(ot, n, cType, lb) {}

  explicit LogicTermImpl(const TermInterface &other) {
    this->id = other.getID();
    this->name = other.getName();
    this->nodes.clear();
    for (auto &it : other.getNodes())
      this->nodes.push_back(static_cast<LogicTerm>(it));
    opType = other.getOpType();
    c_type = other.getCType();
    value = other.getBoolValue();
    i_value = other.getIntValue();
    f_value = other.getFloatValue();
    bv_value = other.getBitVectorValue();
    bv_size = other.getBitVectorSize();
    lb = other.getLogic();
    depth = other.getDepth();
  }
};
}; // namespace logicbase

#endif // LogicTermImpl_HPP