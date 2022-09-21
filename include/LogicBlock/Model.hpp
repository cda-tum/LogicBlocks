#ifndef LOGICBLOCK_MODEL_H
#define LOGICBLOCK_MODEL_H

#include "LogicTerm/LogicTerm.hpp"

namespace logicbase {
    class Model {
    protected:
        Result result = Result::NDEF;

    public:
        Model() = default;
        explicit Model(Result result):
            result(result) {}
        virtual ~Model() = default;

        Result getResult() { return result; };
        void   setResult(Result res) { result = res; };

        virtual int       getIntValue(const LogicTerm& a, LogicBlock* lb)  = 0;
        virtual LogicTerm getValue(const LogicTerm& a, LogicBlock* lb)     = 0;
        virtual bool      getBoolValue(const LogicTerm& a, LogicBlock* lb) = 0;
        virtual double    getRealValue(const LogicTerm& a, LogicBlock* lb) = 0;
        virtual uint64_t  getBitvectorValue(const LogicTerm& a,
                                            LogicBlock*      lb)                = 0;
    };
} // namespace logicbase
#endif // LOGICBLOCK_MODEL_H
