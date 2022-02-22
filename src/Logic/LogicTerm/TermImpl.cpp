#include "TermImpl.hpp"
#include "../LogicUtil/util_logicterm.h"
#include "Logic.hpp"
#include "utils/util.hpp"
#include <bitset>

using namespace logicbase;

TermImpl::TermImpl(OpType ot, const std::initializer_list<LogicTerm> &n,
                   CType cType, Logic *lb)
    : lb(lb), id(getNextId(lb)), depth(logicutil::getMax(n)),
      name(getStrRep(ot)), opType(ot), c_type(cType) {
  nodes.clear();
  for (auto &it : n)
    nodes.push_back(it);
}

TermImpl::TermImpl(OpType ot, const std::vector<LogicTerm> &n, CType cType,
                   Logic *lb)
    : lb(lb), id(getNextId(lb)), depth(logicutil::getMax(n)),
      name(getStrRep(ot)), opType(ot), c_type(cType) {
  nodes.clear();
  for (auto &it : n)
    nodes.push_back(it);
}

TermImpl::TermImpl(OpType ot, const LogicTerm &a, CType cType, Logic *lb)
    : TermImpl(ot, {a}, cType, lb) {}
TermImpl::TermImpl(OpType ot, const LogicTerm &a, const LogicTerm &b,
                   CType cType, Logic *lb)
    : TermImpl(ot, {a, b}, cType, lb) {}
TermImpl::TermImpl(OpType ot, const LogicTerm &a, const LogicTerm &b,
                   const LogicTerm &c, CType cType, Logic *lb)
    : TermImpl(ot, {a, b, c}, cType, lb) {}

TermImpl::TermImpl(const TermInterface &other) {
  lb = other.getLogic();
  id = other.getID();
  depth = other.getDepth();
  name = other.getDepth();
  opType = other.getOpType();
  value = other.getBoolValue();
  i_value = other.getIntValue();
  f_value = other.getFloatValue();
  bv_value = other.getBitVectorValue();
  bv_size = other.getBitVectorSize();
  c_type = other.getCType();
  nodes.clear();
  nodes.insert(nodes.end(), other.getNodes().begin(), other.getNodes().end());
}

std::string TermImpl::getStrRep(OpType opType) const {
  std::stringstream os;
  switch (opType) {
  case OpType::Constant:
    os << "<CONST";
    break;
  case OpType::Variable:
    os << "VAR";
    break;
  case OpType::AND:
    os << "<AND ";
    break;
  case OpType::OR:
    os << "<OR ";
    break;
  case OpType::ITE:
    os << "<ITE ";
    break;
  case OpType::NEG:
    os << "<NEG ";
    break;
  case OpType::EQ:
    os << "<EQ ";
    break;
  case OpType::XOR:
    os << "<XOR ";
    break;
  case OpType::IMPL:
    os << "<IMPL ";
    break;
  case OpType::ADD:
    os << "<ADD ";
    break;
  case OpType::SUB:
    os << "<SUB ";
    break;
  case OpType::MUL:
    os << "<MUL ";
    break;
  case OpType::DIV:
    os << "<DIV ";
    break;
  case OpType::GT:
    os << "<GT ";
    break;
  case OpType::LT:
    os << "<LT ";
    break;
  default:
    os << "<ERROR TYPE";
    break;
  }
  return os.str();
}

void TermImpl::print(std::ostream &os) const {
  os << getStrRep(opType);
  if (opType == OpType::Variable) {
    os << " " << toString(c_type);
    os << " " << (name.empty() ? std::to_string(id) : name);
  }
  if (opType == OpType::Constant) {
    os << " " << toString(c_type);
    os << " " << getValue();
  }
  for (const auto &n : nodes) {
    n.print(os);
    os << ", ";
  }
  if (opType != OpType::Variable && opType != OpType::Constant) {
    os << ">";
  }
}

bool TermImpl::getBoolValue() const {
  switch (c_type) {
  case CType::BOOL:
    return value;
    break;
  case CType::INT:
    return i_value != 0;
    break;
  case CType::REAL:
    return f_value != 0;
    break;
  case CType::BITVECTOR:
    return bv_value != 0;
    break;
  default:
    return false;
    break;
  }
}

int TermImpl::getIntValue() const {
  switch (c_type) {
  case CType::BOOL:
    return value ? 1 : 0;
    break;
  case CType::INT:
    return i_value;
    break;
  case CType::REAL:
    return std::floor(f_value);
    break;
  case CType::BITVECTOR:
    return bv_value;
    break;
  default:
    return INFINITY;
    break;
  }
}

double TermImpl::getFloatValue() const {
  switch (c_type) {
  case CType::BOOL:
    return value ? 1.0 : 0.0;
    break;
  case CType::INT:
    return i_value;
    break;
  case CType::REAL:
    return f_value;
    break;
  case CType::BITVECTOR:
    throw std::runtime_error("no viable conversion from real to bitvector");
    break;
  default:
    return float(INFINITY);
    break;
  }
}

unsigned long long TermImpl::getBitVectorValue() const {
  switch (c_type) {
  case CType::BOOL:
    return value ? 1.0 : 0.0;
    break;
  case CType::INT:
    return i_value;
    break;
  case CType::REAL:
    throw std::runtime_error("no viable conversion from real to bitvector");
    break;
  case CType::BITVECTOR:
    return bv_value & static_cast<unsigned long long>(std::pow(2, bv_size)) - 1;
    break;
  default:
    return float(INFINITY);
    break;
  }
}

short TermImpl::getBitVectorSize() const {
  switch (c_type) {
  case CType::BOOL:
    return 1;
    break;
  case CType::INT:
    return 32;
    break;
  case CType::REAL:
    throw std::runtime_error("no viable conversion from real to bitvector");
    break;
  case CType::BITVECTOR:
    return bv_size;
    break;
  default:
    return short(INFINITY);
    break;
  }
}

std::string TermImpl::getValue() const {
  if (c_type == CType::BOOL)
    return std::to_string(getBoolValue());
  if (c_type == CType::INT)
    return std::to_string(getIntValue());
  if (c_type == CType::REAL)
    return std::to_string(getFloatValue());
  if (c_type == CType::BITVECTOR)
    return std::bitset<32>{getBitVectorValue()}.to_string();
  throw std::runtime_error("Invalid CType of LogicTerm");
}

bool TermImpl::deepEquals(const TermImpl &other) const {
  if (getOpType() == OpType::Variable && getID() == other.getID())
    return true;
  if (getDepth() != other.getDepth())
    return false;
  if (getOpType() != other.getOpType())
    return false;
  if (getName() != other.getName())
    return false;
  if (getNodes().size() != other.getNodes().size())
    return false;
  if (getID() != other.getID())
    return false;
  if (getCType() != other.getCType())
    return false;
  for (size_t i = 0; i < getNodes().size(); ++i) {
    if (!getNodes()[i].deepEquals(other.getNodes()[i]))
      return false;
  }
  return true;
}