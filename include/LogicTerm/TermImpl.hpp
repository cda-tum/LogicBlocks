#ifndef TermImpl_HPP
#define TermImpl_HPP

#include "Logic.hpp"

#include <bitset>
#include <utility>

namespace logicbase {
    class TermImpl {
    protected:
        Logic*      lb    = nullptr;
        int64_t     id    = 0;
        uint64_t    depth = 0U;
        std::string name{};

        OpType                 opType  = OpType::Variable;
        bool                   value   = false;
        int                    iValue  = 0;
        double                 fValue  = 0.;
        uint64_t               bvValue = 0U;
        int16_t                bvSize  = 0;
        std::vector<LogicTerm> nodes{};
        CType                  cType = CType::BOOL;

    public:
        explicit TermImpl(bool v):
            opType(OpType::Constant), value(v), cType(CType::BOOL) {}

        explicit TermImpl(int32_t v):
            opType(OpType::Constant), iValue(v), cType(CType::INT) {}

        explicit TermImpl(double v):
            opType(OpType::Constant), fValue(v), cType(CType::REAL) {}

        explicit TermImpl(uint64_t v, int16_t bvSize):
            opType(OpType::Constant), bvValue(v), bvSize(bvSize), cType(CType::BITVECTOR) {}

        explicit TermImpl(Logic* lb = nullptr):
            lb(lb), id(getNextId(lb)), name(std::to_string(id)) {}

        explicit TermImpl(std::string name, Logic* lb = nullptr):
            lb(lb), id(getNextId(lb)), name(std::move(name)) {}

        explicit TermImpl(OpType opType, std::string name, CType cType,
                          Logic* lb = nullptr, int16_t bvSize = 0):
            lb(lb),
            id(getNextId(lb)), name(std::move(name)), opType(opType), bvSize(bvSize), cType(cType) {}

        explicit TermImpl(std::string name, int64_t id, Logic* lb = nullptr):
            lb(lb), id(id), name(std::move(name)) {}

        explicit TermImpl(CType cType, Logic* lb = nullptr):
            lb(lb), id(getNextId(lb)), name(std::to_string(id)), cType(cType) {}

        explicit TermImpl(std::string name, CType cType, Logic* lb = nullptr,
                          int16_t bvSize = 0):
            lb(lb),
            id(getNextId(lb)), name(std::move(name)), bvSize(bvSize), cType(cType) {}

        explicit TermImpl(std::string name, int64_t id, CType cType,
                          Logic* lb = nullptr):
            lb(lb),
            id(id), name(std::move(name)), cType(cType) {}

        explicit TermImpl(OpType ot, const std::initializer_list<LogicTerm>& n,
                          CType cType = CType::BOOL, Logic* lb = nullptr);

        explicit TermImpl(OpType ot, const std::vector<LogicTerm>& n,
                          CType cType = CType::BOOL, Logic* lb = nullptr);

        explicit TermImpl(OpType ot, const LogicTerm& a, CType cType = CType::BOOL,
                          Logic* lb = nullptr);
        explicit TermImpl(OpType ot, const LogicTerm& a, const LogicTerm& b,
                          CType cType = CType::BOOL, Logic* lb = nullptr);
        explicit TermImpl(OpType ot, const LogicTerm& a, const LogicTerm& b,
                          const LogicTerm& c, CType cType = CType::BOOL,
                          Logic* lb = nullptr);
        TermImpl(const TermImpl& other);
        explicit TermImpl(const LogicTerm& other);

        static int64_t getNextId(Logic* lb = nullptr) {
            if (lb == nullptr) {
                return gid++;
            }
            {
                return lb->getNextId();
            }
        }
        [[nodiscard]] static std::string getStrRep(OpType opType);

        void print(std::ostream& os) const;
        void prettyPrint(std::ostream& os, int printDepth = 0, bool isNeg = false, bool printNL = false, bool lastNL = false) const;

        [[nodiscard]] int64_t getID() const { return id; }

        [[nodiscard]] const std::string& getName() const { return name; }

        [[nodiscard]] std::string getConstantValue() const;

        [[nodiscard]] OpType getOpType() const { return opType; }

        [[nodiscard]] CType getCType() const { return cType; }

        [[nodiscard]] const std::vector<LogicTerm>& getNodes() const { return nodes; }

        [[nodiscard]] bool getBoolValue() const;

        [[nodiscard]] int getIntValue() const;

        [[nodiscard]] double getFloatValue() const;

        [[nodiscard]] uint64_t getBitVectorValue() const;

        [[nodiscard]] int16_t getBitVectorSize() const;

        [[nodiscard]] std::string getValue() const;

        [[nodiscard]] uint64_t getDepth() const { return depth; }

        [[nodiscard]] bool deepEquals(const TermImpl& other) const;

        [[nodiscard]] Logic* getLogic() const { return lb; }

        static int64_t gid;
        static int64_t getGID() { return gid; }

        static void reset() { gid = 0; }
    };
} // namespace logicbase
#endif // TermImpl_HPP
