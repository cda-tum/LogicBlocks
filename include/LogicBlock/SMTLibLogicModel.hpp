#pragma once

#include "LogicBlock.hpp"
#include "LogicBlock/Model.hpp"
#include "LogicBlock/SMTLibLogicBlock.hpp"

#include <regex>
#include <utility>

namespace smtliblogic {
    using namespace logicbase;

    class SMTLibLogicModel: public Model {
    protected:
        std::string modelString;

        const std::basic_regex<char> lineRegex    = std::regex(R"(\(define-fun (.*) \(\) (.*) (.*)\))");
        const std::basic_regex<char> bvTypeRegex  = std::regex(R"(\(_ BitVector (\d+)\))");
        const std::basic_regex<char> bvValueRegex = std::regex(R"(#x(\d+))");

    public:
        SMTLibLogicModel(std::string modelString):
            modelString(std::move(modelString)) {}
        int       getIntValue(const LogicTerm& a, [[maybe_unused]] LogicBlock* lb) override;
        LogicTerm getValue(const LogicTerm& a, [[maybe_unused]] LogicBlock* lb) override;
        bool      getBoolValue(const LogicTerm& a, [[maybe_unused]] LogicBlock* lb) override;
        double    getRealValue(const LogicTerm& a, [[maybe_unused]] LogicBlock* lb) override;
        uint64_t  getBitvectorValue(const LogicTerm& a, [[maybe_unused]] LogicBlock* lb) override;

        std::string getModelString() const { return modelString; }

    private:
        std::string getTermString(const LogicTerm& a);
        std::string getTermType(const LogicTerm& a);
        std::string getTermValue(const LogicTerm& a);
    };
} // namespace smtliblogic
