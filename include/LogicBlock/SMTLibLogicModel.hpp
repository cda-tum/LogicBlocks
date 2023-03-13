#ifndef LOGICBLOCKS_SMTLIBLOGICMODEL_HPP
#define LOGICBLOCKS_SMTLIBLOGICMODEL_HPP

#include "LogicBlock.hpp"
#include "LogicBlock/Model.hpp"
#include "LogicBlock/SMTLibLogicBlock.hpp"

#include <utility>

namespace smtliblogic {
    using namespace logicbase;

    class SMTLibLogicModel: public Model {
    protected:
        std::string modelString;

    public:
        SMTLibLogicModel(std::string modelString):
            modelString(std::move(modelString)) {}
        int       getIntValue(const LogicTerm& a, LogicBlock* lb) override;
        LogicTerm getValue(const LogicTerm& a, LogicBlock* lb) override;
        bool      getBoolValue(const LogicTerm& a, LogicBlock* lb) override;
        double    getRealValue(const LogicTerm& a, LogicBlock* lb) override;
        uint64_t  getBitvectorValue(const LogicTerm& a, LogicBlock* lb) override;

        std::string getModelString() const { return modelString; }

    private:
        std::string getTermString(const LogicTerm& a);
        std::string getTermType(const LogicTerm& a);
        std::string getTermValue(const LogicTerm& a);
    };
} // namespace smtliblogic
#endif //LOGICBLOCKS_SMTLIBLOGICMODEL_HPP
