
#include "LogicBlock/SMTLibLogicModel.hpp"

#include <regex>

std::string smtliblogic::SMTLibLogicModel::getTermString(const LogicTerm& a) {
    std::stringstream ss(modelString);
    std::string       line;

    const auto  regex = std::regex("\\(define-fun (.*) \\(\\) (.*) (.*)\\)");
    std::smatch m;
    while (std::getline(ss, line)) {
        if (std::regex_search(line, m, regex)) {
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

    const auto  regex = std::regex(R"(\(define-fun (.*) \(\) (.*) (.*)\))");
    std::smatch m;

    if (std::regex_search(termString, m, regex)) {
        if (m.size() == 4) {
            return m[3];
        }
    }

    return {};
}
int smtliblogic::SMTLibLogicModel::getIntValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    const auto        type  = getTermType(a);
    if (type != "Int") {
        return 0;
    }
    if (value.empty()) {
        return 0;
    }
    return std::stoi(value);
}
bool smtliblogic::SMTLibLogicModel::getBoolValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    const auto        type  = getTermType(a);
    if (type != "Bool") {
        return false;
    }
    if (value.empty()) {
        return false;
    }
    return value == "true";
}
double smtliblogic::SMTLibLogicModel::getRealValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    const auto        type  = getTermType(a);
    if (type != "Real") {
        return 0.0;
    }
    if (value.empty()) {
        return 0.0;
    }
    return std::stod(value);
}
uint64_t smtliblogic::SMTLibLogicModel::getBitvectorValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    if (value.empty()) {
        return 0;
    }
    const auto type = getTermType(a);

    const auto  typeRegex = std::regex(R"(\(_ BitVector (\d+)\))");
    std::smatch m;
    if (std::regex_search(type, m, typeRegex)) {
        if (m.size() == 2) {
            if (std::stoi(m[1]) != a.getBitVectorSize()) {
                return 0;
            }
        } else {
            return 0;
        }
    } else {
        return 0;
    }
    const auto regex = std::regex(R"(#x(\d+))");

    if (std::regex_search(value, m, regex)) {
        if (m.size() == 2) {
            return std::stoull(m[1], 0, 2);
        }
    }
    return 0;
}
logicbase::LogicTerm smtliblogic::SMTLibLogicModel::getValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    if (a.getOpType() != OpType::Variable) {
        throw std::runtime_error("TermInterface::getValue: not a variable");
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
            "TermInterface::getValue: not supported for this CType");
}
std::string smtliblogic::SMTLibLogicModel::getTermType(const logicbase::LogicTerm& a) {
    std::string const termString = getTermString(a);

    const auto  regex = std::regex(R"(\(define-fun (.*) \(\) (.*) (.*)\))");
    std::smatch m;

    if (std::regex_search(termString, m, regex)) {
        if (m.size() == 4) {
            return m[2];
        }
    }

    return {};
}
