#ifndef TermImpl_HPP
#define TermImpl_HPP

#include "Logic.hpp"

#include <bitset>
#include <utility>

namespace logicbase {
    class TermImpl {
    protected:
        Logic*      lb    = nullptr;
        uint64_t    id    = 0;
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

        static inline uint64_t gid = 1;

    public:
        explicit TermImpl(bool v):
            opType(OpType::Constant), value(v) {}

        explicit TermImpl(int32_t v):
            opType(OpType::Constant), iValue(v), cType(CType::INT) {}

        explicit TermImpl(double v):
            opType(OpType::Constant), fValue(v), cType(CType::REAL) {}

        explicit TermImpl(uint64_t v, int16_t bvs):
            opType(OpType::Constant), bvValue(v), bvSize(bvs), cType(CType::BITVECTOR) {}

        explicit TermImpl(Logic* logic = nullptr):
            lb(logic), id(getNextId(lb)), name(std::to_string(id)) {}

        explicit TermImpl(std::string n, Logic* logic = nullptr):
            lb(logic), id(getNextId(lb)), name(std::move(n)) {}

        explicit TermImpl(OpType op, std::string n, CType type,
                          Logic* logic = nullptr, int16_t bvs = 0):
            lb(logic),
            id(getNextId(lb)), name(std::move(n)), opType(op), bvSize(bvs), cType(type) {}

        explicit TermImpl(std::string n, const uint64_t identifier, Logic* logic = nullptr):
            lb(logic), id(identifier), name(std::move(n)) {}

        explicit TermImpl(CType type, Logic* logic = nullptr):
            lb(logic), id(getNextId(lb)), name(std::to_string(id)), cType(type) {}

        explicit TermImpl(std::string n, CType type, Logic* logic = nullptr,
                          int16_t bvs = 0):
            lb(logic),
            id(getNextId(lb)), name(std::move(n)), bvSize(bvs), cType(type) {}

        explicit TermImpl(std::string n, const uint64_t identifier, CType type,
                          Logic* logic = nullptr):
            lb(logic),
            id(identifier), name(std::move(n)), cType(type) {}

        explicit TermImpl(OpType op, const std::initializer_list<LogicTerm>& n,
                          CType type = CType::BOOL, Logic* logic = nullptr);

        explicit TermImpl(OpType op, const std::vector<LogicTerm>& n,
                          CType type = CType::BOOL, Logic* logic = nullptr);

        explicit TermImpl(OpType op, const LogicTerm& a, CType type = CType::BOOL,
                          Logic* logic = nullptr);
        explicit TermImpl(OpType op, const LogicTerm& a, const LogicTerm& b,
                          CType type = CType::BOOL, Logic* logic = nullptr);
        explicit TermImpl(OpType op, const LogicTerm& a, const LogicTerm& b,
                          const LogicTerm& c, CType type = CType::BOOL,
                          Logic* logic = nullptr);
        TermImpl(const TermImpl& other);
        explicit TermImpl(const LogicTerm& other);

        static uint64_t getNextId(Logic* logic = nullptr) {
            if (logic == nullptr) {
                return gid++;
            }
            return logic->getNextId();
        }
        [[nodiscard]] static std::string getStrRep(OpType op);

        void print(std::ostream& os) const;
        void prettyPrint(std::ostream& os, int printDepth = 0, bool isNeg = false, bool printNL = false, bool lastNL = false) const;

        [[nodiscard]] uint64_t getID() const { return id; }

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

        static uint64_t getGID() { return gid; }

        static void reset() { gid = 0; }
    };
} // namespace logicbase
#endif // TermImpl_HPP
