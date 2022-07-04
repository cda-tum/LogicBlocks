#include "LogicTerm/TermImpl.hpp"

#include "LogicUtil/util_logicterm.hpp"

#include <bitset>

using namespace logicbase;

TermImpl::TermImpl(OpType ot, const std::initializer_list<LogicTerm>& n,
                   CType cType, Logic* lb):
    lb(lb),
    id(getNextId(lb)), depth(logicutil::getMax(n)),
    name(getStrRep(ot)), opType(ot), bv_size(logicutil::getMaxBVSize(n)),
    nodes(n), c_type(cType) {}

TermImpl::TermImpl(OpType ot, const std::vector<LogicTerm>& n, CType cType,
                   Logic* lb):
    lb(lb),
    id(getNextId(lb)), depth(logicutil::getMax(n)),
    name(getStrRep(ot)), opType(ot), bv_size(logicutil::getMaxBVSize(n)),
    nodes(n), c_type(cType) {}

TermImpl::TermImpl(OpType ot, const LogicTerm& a, CType cType, Logic* lb):
    TermImpl(ot, {a}, cType, lb) {}
TermImpl::TermImpl(OpType ot, const LogicTerm& a, const LogicTerm& b,
                   CType cType, Logic* lb):
    TermImpl(ot, {a, b}, cType, lb) {}
TermImpl::TermImpl(OpType ot, const LogicTerm& a, const LogicTerm& b,
                   const LogicTerm& c, CType cType, Logic* lb):
    TermImpl(ot, {a, b, c}, cType, lb) {}

TermImpl::TermImpl(const LogicTerm& other) {
    lb       = other.getLogic();
    id       = other.getID();
    depth    = other.getDepth();
    name     = other.getName();
    opType   = other.getOpType();
    value    = other.getBoolValue();
    i_value  = other.getIntValue();
    f_value  = other.getFloatValue();
    bv_value = other.getBitVectorValue();
    bv_size  = other.getBitVectorSize();
    c_type   = other.getCType();
    nodes.clear();
    nodes.insert(nodes.end(), other.getNodes().begin(), other.getNodes().end());
}
TermImpl::TermImpl(const TermImpl& other) {
    lb       = other.getLogic();
    id       = other.getID();
    depth    = other.getDepth();
    name     = other.getName();
    opType   = other.getOpType();
    value    = other.getBoolValue();
    i_value  = other.getIntValue();
    f_value  = other.getFloatValue();
    bv_value = other.getBitVectorValue();
    bv_size  = other.getBitVectorSize();
    c_type   = other.getCType();
    nodes.clear();
    nodes.insert(nodes.end(), other.getNodes().begin(), other.getNodes().end());
}

std::string TermImpl::getStrRep(OpType opType) {
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
        case OpType::BIT_AND:
            os << "<BV_AND ";
            break;
        case OpType::BIT_OR:
            os << "<BV_OR ";
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
        case OpType::BIT_EQ:
            os << "<BV_EQ ";
            break;
        case OpType::BIT_XOR:
            os << "<BV_XOR ";
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
        case OpType::GTE:
            os << "<GTE ";
            break;
        case OpType::LTE:
            os << "<LTE ";
            break;
        default:
            os << "<ERROR TYPE";
            break;
    }
    return os.str();
}

void TermImpl::print(std::ostream& os) const {
    os << getStrRep(opType);
    if (opType == OpType::Variable) {
        os << " " << toString(c_type);
        os << " " << (name.empty() ? std::to_string(id) : name);
    } else if (opType == OpType::Constant) {
        os << " " << toString(c_type);
        os << " " << getValue();
    } else {
        for (const auto& n: nodes) {
            n.print(os);
            os << ", ";
        }
    }
    if (opType != OpType::Variable && opType != OpType::Constant) {
        os << ">";
    }
}

bool TermImpl::getBoolValue() const {
    switch (c_type) {
        case CType::BOOL:
            return value;
        case CType::INT:
            return i_value != 0;
        case CType::REAL:
            return f_value != 0;
        case CType::BITVECTOR:
            return bv_value != 0;
        default:
            return false;
    }
}

int TermImpl::getIntValue() const {
    switch (c_type) {
        case CType::BOOL:
            return value ? 1 : 0;
        case CType::INT:
            return i_value;
        case CType::REAL:
            return std::floor(f_value);
        case CType::BITVECTOR:
            return static_cast<int>(bv_value);
        default:
            return std::numeric_limits<int>::infinity();
    }
}

double TermImpl::getFloatValue() const {
    switch (c_type) {
        case CType::BOOL:
            return value ? 1.0 : 0.0;
        case CType::INT:
            return i_value;
        case CType::REAL:
            return f_value;
        case CType::BITVECTOR:
            return static_cast<double>(bv_value);
        default:
            return std::numeric_limits<double>::infinity();
    }
}

unsigned long long TermImpl::getBitVectorValue() const {
    switch (c_type) {
        case CType::BOOL:
            return value ? 1.0 : 0.0;
        case CType::INT:
            return i_value;
        case CType::REAL:
            return static_cast<unsigned long long>(f_value);
        case CType::BITVECTOR:
            return bv_value & (static_cast<unsigned long long>(std::pow(2, bv_size)) - 1U);
        default:
            return std::numeric_limits<unsigned long long>::infinity();
    }
}

short TermImpl::getBitVectorSize() const {
    switch (c_type) {
        case CType::BOOL:
            return 1;
        case CType::INT:
            return 32;
        case CType::REAL:
            return 256;
        case CType::BITVECTOR:
            return bv_size;
        default:
            return std::numeric_limits<short>::infinity();
    }
}

std::string TermImpl::getValue() const {
    if (c_type == CType::BOOL)
        return std::to_string(getBoolValue());
    if (c_type == CType::INT)
        return std::to_string(getIntValue());
    if (c_type == CType::REAL)
        return std::to_string(getFloatValue());
    if (c_type == CType::BITVECTOR) {
        return std::bitset<256U>{getBitVectorValue()}.to_string().substr(
                256U - bv_size, bv_size);
    }
    throw std::runtime_error("Invalid CType of LogicTerm");
}

bool TermImpl::deepEquals(const TermImpl& other) const {
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
    for (size_t i = 0U; i < getNodes().size(); ++i) {
        if (!getNodes()[i].deepEquals(other.getNodes()[i])) {
            return false;
        }
    }
    return true;
}
void TermImpl::prettyPrint(std::ostream& os, int depth) const {
    for (int i = 0; i < depth; ++i) {
        os << "  ";
    }
    os << getStrRep(opType);
    if (opType == OpType::Variable) {
        os << " " << toString(c_type);
        os << " " << (name.empty() ? std::to_string(id) : name);
    } else if (opType == OpType::Constant) {
        os << " " << toString(c_type);
        os << " " << getValue();
    } else {
        os << std::endl;
        for (const auto& n: nodes) {
            n.prettyPrint(os, depth + 1);
        }
    }
    if (opType != OpType::Variable && opType != OpType::Constant) {
        os << std::endl;
        for (int i = 0; i < depth; ++i) {
            os << "  ";
        }
        os << ">";
        os << std::endl;
    }
}
