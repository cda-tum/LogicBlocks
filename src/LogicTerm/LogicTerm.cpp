#include "LogicTerm/LogicTerm.hpp"

#include "LogicUtil/util_logic.hpp"
#include "LogicUtil/util_logicterm.hpp"

namespace logicbase {
    TermType  LogicTerm::termType                = TermType::BASE;
    long long TermImpl::gid                      = 1;
    bool      LogicTerm::useBitVectorConversions = false;

    std::shared_ptr<TermImpl> makeLogicTerm(const bool value) {
        return std::make_shared<TermImpl>(value);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(const int value) {
        return std::make_shared<TermImpl>(value);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(const double value) {
        return std::make_shared<TermImpl>(value);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(const unsigned long long value,
                                            short                    bv_size) {
        return std::make_shared<TermImpl>(value, bv_size);
    }
    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const std::string& name,
                                            CType cType, Logic* lb) {
        return std::make_shared<TermImpl>(opType, name, cType, lb);
    }

    std::shared_ptr<TermImpl> makeLogicTerm(const char* name = "", CType cType,
                                            Logic* lb, short bv_size) {
        return std::make_shared<TermImpl>(name, cType, lb, bv_size);
    }

    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const LogicTerm& a,
                                            const LogicTerm& b) {
        Logic* lb = logicutil::getValidLogic_ptr(a, b);

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
        Logic* lb          = logicutil::getValidLogic_ptr(a, b, c);
        CType  targetCType = logicutil::getTargetCType(b, c, opType);
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

    long long LogicTerm::getID() const {
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

    int LogicTerm::getIntValue() const {
        return pImpl->getIntValue();
    }

    double LogicTerm::getFloatValue() const {
        return pImpl->getFloatValue();
    }

    unsigned long long LogicTerm::getBitVectorValue() const {
        return pImpl->getBitVectorValue();
    }

    short LogicTerm::getBitVectorSize() const {
        return pImpl->getBitVectorSize();
    }

    const std::string& LogicTerm::getName() const {
        return pImpl->getName();
    }

    std::shared_ptr<TermImpl> LogicTerm::getImplementation() const {
        return pImpl;
    }

    bool LogicTerm::deepEquals(const LogicTerm& other) const {
        return this->pImpl->deepEquals(*other.getImplementation());
    }

    unsigned long long LogicTerm::getDepth() const {
        return pImpl->getDepth();
    }

    unsigned long long LogicTerm::getMaxChildrenDepth() const {
        unsigned long long max = 0;
        for (const LogicTerm& t: pImpl->getNodes()) {
            unsigned long long d = t.getMaxChildrenDepth();
            if (d > max)
                max = d;
        }
        return max + 1;
    };

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
    void LogicTerm::prettyPrint(std::ostream& os, int depth) const {
        pImpl->prettyPrint(os, depth);
    }

} // namespace logicbase
