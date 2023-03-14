
#include "LogicBlock/SMTLibLogicModel.hpp"

std::string smtliblogic::SMTLibLogicModel::getTermString(const LogicTerm& a) {
    std::stringstream ss(modelString);
    std::string       line;

    std::smatch m;
    while (std::getline(ss, line)) {
        if (std::regex_search(line, m, lineRegex)) {
            if (m.size() == 4) {
                if (m[1] == a.getName()) {
                    return line;
                }
            }
        }
    }
    return {};
}
std::string smtliblogic::SMTLibLogicModel::getTermValue(const logicbase::LogicTerm& a) {
    std::string const termString = getTermString(a);

    std::smatch m;

    if (std::regex_search(termString, m, lineRegex)) {
        if (m.size() == 4) {
            return m[3];
        }
    }

    return {};
}
int smtliblogic::SMTLibLogicModel::getIntValue(const logicbase::LogicTerm& a, [[maybe_unused]] logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    const auto        type  = getTermType(a);
    if (type != "Int") {
        throw std::runtime_error("Type mismatch, expected int got " + type);
    }
    if (value.empty()) {
        return 0;
    }
    return std::stoi(value);
}
bool smtliblogic::SMTLibLogicModel::getBoolValue(const logicbase::LogicTerm& a, [[maybe_unused]] logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    const auto        type  = getTermType(a);
    if (type != "Bool") {
        throw std::runtime_error("Type mismatch, expected bool got " + type);
    }
    if (value.empty()) {
        return false;
    }
    return value == "true";
}
double smtliblogic::SMTLibLogicModel::getRealValue(const logicbase::LogicTerm& a, [[maybe_unused]] logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    const auto        type  = getTermType(a);
    if (type != "Real") {
        throw std::runtime_error("Type mismatch, expected real got " + type);
    }
    if (value.empty()) {
        return 0.0;
    }
    return std::stod(value);
}
uint64_t smtliblogic::SMTLibLogicModel::getBitvectorValue(const logicbase::LogicTerm& a, [[maybe_unused]] logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    if (value.empty()) {
        return 0;
    }
    const auto type = getTermType(a);

    std::smatch m;
    if (std::regex_search(type, m, bvTypeRegex)) {
        if (m.size() == 2) {
            if (std::stoi(m[1]) != a.getBitVectorSize()) {
                throw std::runtime_error("bitvector size mismatch");
            }
        } else {
            throw std::runtime_error("bitvector size not found");
        }
    } else {
        throw std::runtime_error("Type mismatch, expected bitvector got " + type);
    }

    if (std::regex_search(value, m, bvValueRegex)) {
        if (m.size() == 2) {
            return std::stoull(m[1], 0, 2);
        }
    }
    return 0;
}
logicbase::LogicTerm smtliblogic::SMTLibLogicModel::getValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    if (a.getOpType() != OpType::Variable) {
        throw std::runtime_error("Not a variable");
    }
    if (a.getCType() == CType::BOOL) {
        return LogicTerm(getBoolValue(a, lb));
    }
    if (a.getCType() == CType::INT) {
        return LogicTerm(getIntValue(a, lb));
    }
    if (a.getCType() == CType::REAL) {
        return LogicTerm(getRealValue(a, lb));
    }
    if (a.getCType() == CType::BITVECTOR) {
        return {getBitvectorValue(a, lb), a.getBitVectorSize()};
    }
    throw std::runtime_error(
            "Not supported for this CType " + std::to_string(static_cast<int>(a.getCType())));
}
std::string smtliblogic::SMTLibLogicModel::getTermType(const logicbase::LogicTerm& a) {
    std::string const termString = getTermString(a);

    std::smatch m;

    if (std::regex_search(termString, m, lineRegex)) {
        if (m.size() == 4) {
            return m[2];
        }
    }

    return {};
}
