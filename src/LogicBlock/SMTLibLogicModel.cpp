
#include "LogicBlock/SMTLibLogicModel.hpp"

#include <regex>

std::string smtliblogic::SMTLibLogicModel::getTermString(const LogicTerm& a) {
    std::stringstream ss(modelString);
    std::string       line;
    std::getline(ss, line);
    if (line.empty()) {
        return {};
    }

    const auto  regex = std::regex("\\(define-fun (.*) \\(\\) (.*) (.*)\\)");
    std::smatch m;
    if (std::regex_search(line, m, regex)) {
        if (m.size() == 4) {
            if (m[1] == a.getName()) {
                return line;
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
    if (value.empty()) {
        return 0;
    }
    return std::stoi(value);
}
bool smtliblogic::SMTLibLogicModel::getBoolValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
    if (value.empty()) {
        return false;
    }
    return value == "true";
}
double smtliblogic::SMTLibLogicModel::getRealValue(const logicbase::LogicTerm& a, logicbase::LogicBlock* lb) {
    std::string const value = getTermValue(a);
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

    const auto  regex = std::regex(R"(#x(\d+))");
    std::smatch m;

    if (std::regex_search(value, m, regex)) {
        if (m.size() == 2) {
            return std::stoull(m[1], 0, 2);
        }
    }
    return 0;
}
