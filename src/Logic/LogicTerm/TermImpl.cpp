#include "TermImpl.hpp"
#include "Logic.hpp"
#include "utils/util.hpp"

using namespace logicbase;

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

short TermImpl::getBitVectorSize() const { return bv_size; }

std::string TermImpl::getValue() const {
  if (c_type == CType::BOOL)
    return std::to_string(getBoolValue());
  if (c_type == CType::INT)
    return std::to_string(getIntValue());
  if (c_type == CType::REAL)
    return std::to_string(getFloatValue());
  if (c_type == CType::BITVECTOR)
    return std::to_string(getBitVectorValue());
  throw std::runtime_error("Invalid CType of LogicTerm");
}

bool TermImpl::deepEquals(const TermInterface &other) const {
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