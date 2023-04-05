#ifndef LogicTerm_Z3MODEL_H
#define LogicTerm_Z3MODEL_H

#include "LogicBlock/Model.hpp"
#include "LogicBlock/Z3Logic.hpp"
#include "z3++.h"

namespace z3logic {

    using namespace logicbase;

    class Z3Model: public Model {
    protected:
        std::shared_ptr<z3::model>   model;
        std::shared_ptr<z3::context> ctx;

    public:
        Z3Model(std::shared_ptr<z3::context> ctx, const std::shared_ptr<z3::model>& model):
            model(model), ctx(ctx) {}
        int       getIntValue(const LogicTerm& a, LogicBlock* lb) override;
        LogicTerm getValue(const LogicTerm& a, LogicBlock* lb) override;
        bool      getBoolValue(const LogicTerm& a, LogicBlock* lb) override;
        double    getRealValue(const LogicTerm& a, LogicBlock* lb) override;
        uint64_t  getBitvectorValue(const LogicTerm& a, LogicBlock* lb) override;
    };
} // namespace z3logic
#endif // LogicTerm_Z3MODEL_H
