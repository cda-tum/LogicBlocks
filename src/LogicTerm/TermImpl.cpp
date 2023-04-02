#include "LogicTerm/TermImpl.hpp"

#include "LogicUtil/util_logicterm.hpp"

#include <bitset>

using namespace logicbase;

TermImpl::TermImpl(const OpType op, const std::initializer_list<LogicTerm>& n,
                   CType type, Logic* logic):
    lb(logic),
    id(getNextId(logic)), depth(logicutil::getMax(n)),
    name(getStrRep(op)), opType(op), bvSize(logicutil::getMaxBVSize(n)),
    nodes(n), cType(type) {}

TermImpl::TermImpl(const OpType op, const std::vector<LogicTerm>& n, CType type,
                   Logic* logic):
    lb(logic),
    id(getNextId(logic)), depth(logicutil::getMax(n)),
    name(getStrRep(op)), opType(op), bvSize(logicutil::getMaxBVSize(n)),
    nodes(n), cType(type) {}

TermImpl::TermImpl(const OpType op, const LogicTerm& a, CType type, Logic* logic):
    TermImpl(op, {a}, type, logic) {}
TermImpl::TermImpl(OpType op, const LogicTerm& a, const LogicTerm& b,
                   CType type, Logic* logic):
    TermImpl(op, {a, b}, type, logic) {}
TermImpl::TermImpl(OpType op, const LogicTerm& a, const LogicTerm& b,
                   const LogicTerm& c, CType type, Logic* logic):
    TermImpl(op, {a, b, c}, type, logic) {}

TermImpl::TermImpl(const LogicTerm& other):
    lb(other.getLogic()), id(other.getID()), depth(other.getDepth()), name(other.getName()), opType(other.getOpType()), value(other.getBoolValue()), iValue(other.getIntValue()), fValue(other.getFloatValue()), bvValue(other.getBitVectorValue()), bvSize(other.getBitVectorSize()), cType(other.getCType()) {
    nodes.clear();
    nodes.insert(nodes.end(), other.getNodes().begin(), other.getNodes().end());
}
TermImpl::TermImpl(const TermImpl& other):
    lb(other.getLogic()), id(other.getID()), depth(other.getDepth()), name(other.getName()), opType(other.getOpType()), value(other.getBoolValue()), iValue(other.getIntValue()), fValue(other.getFloatValue()), bvValue(other.getBitVectorValue()), bvSize(other.getBitVectorSize()), cType(other.getCType()) {
    nodes.clear();
    nodes.insert(nodes.end(), other.getNodes().begin(), other.getNodes().end());
}

std::string TermImpl::getStrRep(OpType op) {
    std::stringstream os;
    switch (op) {
        case OpType::Constant:
            os << "CONST";
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
        case OpType::BitAnd:
            os << "<BV_AND ";
            break;
        case OpType::BitOr:
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
        case OpType::BitEq:
            os << "<BV_EQ ";
            break;
        case OpType::BitXor:
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
        os << " " << toString(cType);
        os << " " << (name.empty() ? std::to_string(id) : name);
    } else if (opType == OpType::Constant) {
        os << " " << toString(cType);
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
    switch (cType) {
        case CType::BOOL:
            return value;
        case CType::INT:
            return iValue != 0;
        case CType::REAL:
            return fValue != 0;
        case CType::BITVECTOR:
            return bvValue != 0;
        default:
            return false;
    }
}

int32_t TermImpl::getIntValue() const {
    switch (cType) {
        case CType::BOOL:
            return value ? 1 : 0;
        case CType::INT:
            return iValue;
        case CType::REAL:
            return std::floor(fValue);
        case CType::BITVECTOR:
            return static_cast<int>(bvValue);
        default:
            return std::numeric_limits<int>::infinity();
    }
}

double TermImpl::getFloatValue() const {
    switch (cType) {
        case CType::BOOL:
            return value ? 1.0 : 0.0;
        case CType::INT:
            return iValue;
        case CType::REAL:
            return fValue;
        case CType::BITVECTOR:
            return static_cast<double>(bvValue);
        default:
            return std::numeric_limits<double>::infinity();
    }
}

uint64_t TermImpl::getBitVectorValue() const {
    switch (cType) {
        case CType::BOOL:
            return value ? 1.0 : 0.0;
        case CType::INT:
            return iValue;
        case CType::REAL:
            return static_cast<uint64_t>(fValue);
        case CType::BITVECTOR:
            return bvValue & (static_cast<uint64_t>(std::pow(2, bvSize)) - 1U);
        default:
            return std::numeric_limits<uint64_t>::infinity();
    }
}

int16_t TermImpl::getBitVectorSize() const {
    switch (cType) {
        case CType::BOOL:
            return 1;
        case CType::INT:
            return 32;
        case CType::REAL:
            return 256;
        case CType::BITVECTOR:
            return bvSize;
        default:
            return std::numeric_limits<int16_t>::infinity();
    }
}

std::string TermImpl::getValue() const {
    if (cType == CType::BOOL) {
        return std::to_string(static_cast<int>(getBoolValue()));
    }
    if (cType == CType::INT) {
        return std::to_string(getIntValue());
    }
    if (cType == CType::REAL) {
        return std::to_string(getFloatValue());
    }
    if (cType == CType::BITVECTOR) {
        return std::bitset<256U>{getBitVectorValue()}.to_string().substr(
                256U - bvSize, bvSize);
    }
    throw std::runtime_error("Invalid CType of LogicTerm");
}

bool TermImpl::deepEquals(const TermImpl& other) const {
    if (getOpType() == OpType::Variable && getID() == other.getID()) {
        return true;
    }
    if (getDepth() != other.getDepth()) {
        return false;
    }
    if (getOpType() != other.getOpType()) {
        return false;
    }
    if (getName() != other.getName()) {
        return false;
    }
    if (getNodes().size() != other.getNodes().size()) {
        return false;
    }
    if (getCType() != other.getCType()) {
        return false;
    }
    for (size_t i = 0U; i < getNodes().size(); ++i) {
        if (!getNodes()[i].deepEquals(other.getNodes()[i])) {
            return false;
        }
    }
    return true;
}
void TermImpl::prettyPrint(std::ostream& os, int32_t printDepth, bool isNeg, bool printNL, bool lastNL) const {
    if (!isNeg) {
        for (int32_t i = 0; i < printDepth; ++i) {
            os << "  ";
        }
    }
    if (opType != OpType::Variable && opType != OpType::Constant && opType != OpType::NEG && printNL) {
        os << std::endl;
        for (int32_t i = 0; i < printDepth; ++i) {
            os << "  ";
        }
    }
    os << getStrRep(opType);
    if (opType == OpType::Variable) {
        os << " " << toString(cType);
        os << " " << (name.empty() ? std::to_string(id) : name);
    } else if (opType == OpType::Constant) {
        os << " " << toString(cType);
        os << " " << getValue();
    } else {
        if (opType != OpType::NEG) {
            os << std::endl;
        }
        for (auto i = 0U; i < nodes.size(); ++i) {
            nodes[i].prettyPrint(os, printDepth + 1, opType == OpType::NEG, i != 0, i != nodes.size() - 1);
        }
    }
    if (opType != OpType::Variable && opType != OpType::Constant && opType != OpType::NEG) {
        os << std::endl;
        for (int32_t i = 0; i < printDepth; ++i) {
            os << "  ";
        }
        os << ">";
        if (lastNL) {
            os << std::endl;
        }
    }
    if (opType == OpType::NEG) {
        os << " >";
    }
}
std::string TermImpl::getConstantValue() const {
    return getValue();
}
