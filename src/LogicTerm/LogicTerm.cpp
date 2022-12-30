#include "LogicTerm/LogicTerm.hpp"

#include "LogicUtil/util_logic.hpp"
#include "LogicUtil/util_logicterm.hpp"

namespace logicbase {
    std::shared_ptr<TermImpl> makeLogicTerm(const bool value) {
        return std::make_shared<TermImpl>(value);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(const int32_t value) {
        return std::make_shared<TermImpl>(value);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(const double value) {
        return std::make_shared<TermImpl>(value);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(const uint64_t value,
                                            int16_t        bvSize) {
        return std::make_shared<TermImpl>(value, bvSize);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const std::string& name,
                                            CType cType, Logic* lb) {
        return std::make_shared<TermImpl>(opType, name, cType, lb);
    }

    std::shared_ptr<TermImpl> makeLogicTerm(const char* name = "", CType cType,
                                            Logic* lb, int16_t bvSize) {
        return std::make_shared<TermImpl>(name, cType, lb, bvSize);
    }

    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const LogicTerm& a,
                                            const LogicTerm& b) {
        Logic* lb = logicutil::getValidLogicPtr(a, b);

        if (logicutil::isConst(a) || logicutil::isConst(b)) {
            return logicutil::combineConst(a, b, opType, lb);
        }
        if (opType == OpType::AND || opType == OpType::OR) {
            return logicutil::combineTerms(logicutil::getBoolConversion(a),
                                           logicutil::getBoolConversion(b), opType, lb);
        }
        return logicutil::combineTerms(a, b, opType, lb);
    }

    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const LogicTerm& a,
                                            const LogicTerm& b,
                                            const LogicTerm& c) {
        Logic*      lb          = logicutil::getValidLogicPtr(a, b, c);
        const CType targetCType = logicutil::getTargetCType(b, c, opType);
        return std::make_shared<TermImpl>(opType, a, b, c, targetCType, lb);
    }

    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const LogicTerm& a) {
        Logic* lb = a.getLogic();
        if (opType == OpType::NEG) {
            return logicutil::negateTerm(a, lb);
        }
        throw std::runtime_error("Invalid opType");
    }

    void LogicTerm::print(std::ostream& os) const {
        pImpl->print(os);
    }

    uint64_t LogicTerm::getID() const {
        return pImpl->getID();
    }

    const std::vector<LogicTerm>& LogicTerm::getNodes() const {
        return pImpl->getNodes();
    }

    OpType LogicTerm::getOpType() const {
        return pImpl->getOpType();
    }

    CType LogicTerm::getCType() const {
        return pImpl->getCType();
    }

    bool LogicTerm::getBoolValue() const {
        return pImpl->getBoolValue();
    }

    int32_t LogicTerm::getIntValue() const {
        return pImpl->getIntValue();
    }

    double LogicTerm::getFloatValue() const {
        return pImpl->getFloatValue();
    }

    uint64_t LogicTerm::getBitVectorValue() const {
        return pImpl->getBitVectorValue();
    }

    int16_t LogicTerm::getBitVectorSize() const {
        return pImpl->getBitVectorSize();
    }

    const std::string& LogicTerm::getName() const {
        return pImpl->getName();
    }

    std::shared_ptr<TermImpl> LogicTerm::getImplementation() const {
        return pImpl;
    }

    bool LogicTerm::deepEquals(const TermInterface& other) const {
        return this->pImpl->deepEquals(*other.getImplementation());
    }

    uint64_t LogicTerm::getDepth() const {
        return pImpl->getDepth();
    }

    uint64_t LogicTerm::getMaxChildrenDepth() const {
        uint64_t max = 0;
        for (const LogicTerm& t: pImpl->getNodes()) {
            const uint64_t d = t.getMaxChildrenDepth();
            if (d > max) {
                max = d;
            }
        }
        return max + 1;
    }

    Logic* LogicTerm::getLogic() const {
        return pImpl->getLogic();
    }

    LogicTerm LogicTerm::getNeutralElement(OpType opType) {
        switch (opType) {
            case OpType::AND:
                return LogicTerm(true);
            case OpType::OR:
                return LogicTerm(false);
            case OpType::ADD:
                return LogicTerm(0);
            case OpType::MUL:
                return LogicTerm(1);
            default:
                return LogicTerm::noneTerm();
        }
    }
    void LogicTerm::prettyPrint(std::ostream& os, int32_t depth, bool isNeg, bool printNL, bool lastNL) const {
        pImpl->prettyPrint(os, depth, isNeg, printNL, lastNL);
    }
    std::string LogicTerm::getConstantValue() const {
        return pImpl->getConstantValue();
    }

} // namespace logicbase
