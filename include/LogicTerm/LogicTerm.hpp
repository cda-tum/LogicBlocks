#ifndef LOGIC_TERM_H
#define LOGIC_TERM_H

#include "TermImpl.hpp"

#include <cmath>
#include <map>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace logicbase {
    std::shared_ptr<TermImpl> makeLogicTerm(bool value);
    std::shared_ptr<TermImpl> makeLogicTerm(int value);
    std::shared_ptr<TermImpl> makeLogicTerm(double value);
    std::shared_ptr<TermImpl> makeLogicTerm(uint64_t value,
                                            int16_t  bvSize);
    std::shared_ptr<TermImpl> makeLogicTerm(const char* name,
                                            CType       cType = CType::BOOL,
                                            Logic* lb = nullptr, int16_t bvSize = 0);
    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const std::string& name,
                                            CType  cType = CType::BOOL,
                                            Logic* lb    = nullptr);

    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const LogicTerm& a,
                                            const LogicTerm& b);
    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const LogicTerm& a,
                                            const LogicTerm& b, const LogicTerm& c);
    std::shared_ptr<TermImpl> makeLogicTerm(OpType opType, const LogicTerm& a);

    template<typename... Args>
    std::shared_ptr<TermImpl> makeLogicTerm(TermType termType, OpType opType,
                                            Args&&... args) {
        switch (termType) {
            case TermType::BASE:
                return makeLogicTerm(opType, std::forward<Args>(args)...);
            case TermType::CNF:
                throw std::runtime_error("CNF not implemented");
        }
        throw std::invalid_argument("TermType not implemented");
    }

    class LogicTerm: public TermInterface {
    public:
        [[maybe_unused]] static inline TermType termType                = TermType::BASE;
        static inline bool                      useBitVectorConversions = false;

    private:
        std::shared_ptr<TermImpl> pImpl;

        explicit LogicTerm(std::shared_ptr<TermImpl> impl):
            pImpl(std::move(impl)) {}

    public:
        explicit LogicTerm(bool value):
            pImpl(makeLogicTerm(value)) {}
        explicit LogicTerm(int value):
            pImpl(makeLogicTerm(value)) {}
        explicit LogicTerm(double value):
            pImpl(makeLogicTerm(value)) {}
        LogicTerm(uint64_t value, int16_t bvSize):
            pImpl(makeLogicTerm(value, bvSize)) {}

        explicit LogicTerm(CType cType = CType::BOOL, Logic* lb = nullptr):
            pImpl(makeLogicTerm("", cType, lb)) {}
        // LogicTerm(const char *name, CType cType = CType::BOOL, Logic *lb = nullptr)
        //     : pImpl(makeLogicTerm(termType, name, cType, lb)) {}
        explicit LogicTerm(const std::string& name, CType cType = CType::BOOL,
                           Logic* lb = nullptr, int16_t bvSize = 0):
            pImpl(makeLogicTerm(name.c_str(), cType, lb, bvSize)) {}

        LogicTerm(OpType opType, const std::string& name, CType cType = CType::BOOL,
                  Logic* lb = nullptr):
            pImpl(makeLogicTerm(opType, name, cType, lb)) {}

        LogicTerm(const LogicTerm& other):
            pImpl(other.getImplementation()) {}
        LogicTerm(const LogicTerm&& other) noexcept:
            pImpl(other.getImplementation()) {}
        LogicTerm& operator=(const LogicTerm& other) {
            if (this != &other) {
                pImpl = other.getImplementation();
            }
            return *this;
        }
        LogicTerm& operator=(LogicTerm&& other) noexcept {
            if (this != &other) {
                pImpl = other.getImplementation();
            }
            return *this;
        }

        ~LogicTerm() override = default;

        static LogicTerm noneTerm() {
            return LogicTerm(makeLogicTerm(OpType::None, "None", CType::BOOL, nullptr));
        }

        static LogicTerm eq(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::EQ, a, b));
        }

        static LogicTerm neq(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::XOR, a, b));
        }

        static LogicTerm o(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::OR, a, b));
        }

        static LogicTerm a(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::AND, a, b));
        }

        static LogicTerm bvAnd(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::BitAnd, a, b));
        }

        static LogicTerm bvOr(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::BitOr, a, b));
        }

        static LogicTerm bvXor(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::BitXor, a, b));
        }

        static LogicTerm implies(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::IMPL, a, b));
        }

        static LogicTerm ite(const LogicTerm& a, const LogicTerm& b,
                             const LogicTerm& c) {
            return LogicTerm(makeLogicTerm(OpType::ITE, a, b, c));
        }

        static LogicTerm add(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::ADD, a, b));
        }

        static LogicTerm sub(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::SUB, a, b));
        }

        static LogicTerm mul(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::MUL, a, b));
        }

        static LogicTerm div(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::DIV, a, b));
        }

        static LogicTerm gt(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::GT, a, b));
        }

        static LogicTerm lt(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::LT, a, b));
        }

        static LogicTerm gte(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::GTE, a, b));
        }

        static LogicTerm lte(const LogicTerm& a, const LogicTerm& b) {
            return LogicTerm(makeLogicTerm(OpType::LTE, a, b));
        }

        static LogicTerm neg(const LogicTerm& a) {
            return LogicTerm(makeLogicTerm(OpType::NEG, a));
        }

        LogicTerm operator&&(const LogicTerm& other) const {
            return LogicTerm::a(*this, other);
        }

        LogicTerm operator&(const LogicTerm& other) const {
            return LogicTerm::bvAnd(*this, other);
        }

        LogicTerm operator|(const LogicTerm& other) const {
            return LogicTerm::bvOr(*this, other);
        }

        LogicTerm operator^(const LogicTerm& other) const {
            return LogicTerm::bvXor(*this, other);
        }

        LogicTerm operator||(const LogicTerm& other) const {
            return LogicTerm::o(*this, other);
        }

        LogicTerm operator==(const LogicTerm& other) const {
            return LogicTerm::eq(*this, other);
        }

        LogicTerm operator!=(const LogicTerm& other) const {
            return LogicTerm::neq(*this, other);
        }

        LogicTerm operator+(const LogicTerm& other) const {
            return LogicTerm::add(*this, other);
        }

        LogicTerm operator-(const LogicTerm& other) const {
            return LogicTerm::sub(*this, other);
        }

        LogicTerm operator*(const LogicTerm& other) const {
            return LogicTerm::mul(*this, other);
        }

        LogicTerm operator/(const LogicTerm& other) const {
            return LogicTerm::div(*this, other);
        }

        LogicTerm operator>(const LogicTerm& other) const {
            return LogicTerm::gt(*this, other);
        }

        LogicTerm operator<(const LogicTerm& other) const {
            return LogicTerm::lt(*this, other);
        }

        LogicTerm operator>=(const LogicTerm& other) const {
            return LogicTerm::gte(*this, other);
        }

        LogicTerm operator<=(const LogicTerm& other) const {
            return LogicTerm::lte(*this, other);
        }

        LogicTerm operator!() const { return LogicTerm::neg(*this); }

        [[nodiscard]] uint64_t                      getID() const override;
        [[nodiscard]] const std::vector<LogicTerm>& getNodes() const override;
        [[nodiscard]] OpType                        getOpType() const override;
        [[nodiscard]] CType                         getCType() const override;
        [[nodiscard]] bool                          getBoolValue() const override;
        [[nodiscard]] int                           getIntValue() const override;
        [[nodiscard]] double                        getFloatValue() const override;
        [[nodiscard]] uint64_t                      getBitVectorValue() const override;
        [[nodiscard]] int16_t                       getBitVectorSize() const override;
        [[nodiscard]] const std::string&            getName() const override;
        [[nodiscard]] std::string                   getConstantValue() const override;
        [[nodiscard]] std::shared_ptr<TermImpl>     getImplementation() const override;
        [[nodiscard]] Logic*                        getLogic() const override;

        [[nodiscard]] bool deepEquals(const TermInterface& other) const override;

        void print(std::ostream& os) const override;
        void prettyPrint(std::ostream& os, int depth = 0, bool isNeg = false, bool printNL = false, bool lastNL = false) const;

        [[nodiscard]] uint64_t getDepth() const override;

        [[nodiscard]] uint64_t getMaxChildrenDepth() const override;

        static LogicTerm getNeutralElement(OpType opType);

        static void reset() { termType = TermType::BASE; };
    };

} // namespace logicbase
#endif // LOGIC_TERM_H
