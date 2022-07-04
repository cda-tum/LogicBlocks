#ifndef TermImpl_HPP
#define TermImpl_HPP

#include "Logic.hpp"

#include <bitset>
#include <utility>

namespace logicbase {
    class TermImpl {
    protected:
        Logic*             lb    = nullptr;
        long long          id    = 0;
        unsigned long long depth = 0U;
        std::string        name{};

        OpType                 opType   = OpType::Variable;
        bool                   value    = false;
        int                    i_value  = 0;
        double                 f_value  = 0.;
        unsigned long long     bv_value = 0U;
        short                  bv_size  = 0;
        std::vector<LogicTerm> nodes{};
        CType                  c_type = CType::BOOL;

    public:
        explicit TermImpl(bool v):
            opType(OpType::Constant), value(v), c_type(CType::BOOL) {}

        explicit TermImpl(int v):
            opType(OpType::Constant), i_value(v), c_type(CType::INT) {}

        explicit TermImpl(double v):
            opType(OpType::Constant), f_value(v), c_type(CType::REAL) {}

        explicit TermImpl(unsigned long long v, short bv_size):
            opType(OpType::Constant), bv_value(v), bv_size(bv_size), c_type(CType::BITVECTOR) {}

        explicit TermImpl(Logic* lb = nullptr):
            lb(lb), id(getNextId(lb)), name(std::to_string(id)) {}

        explicit TermImpl(std::string name, Logic* lb = nullptr):
            lb(lb), id(getNextId(lb)), name(std::move(name)) {}

        explicit TermImpl(OpType opType, std::string name, CType cType,
                          Logic* lb = nullptr, short bv_size = 0):
            lb(lb),
            id(getNextId(lb)), name(std::move(name)), opType(opType), bv_size(bv_size), c_type(cType) {}

        explicit TermImpl(std::string name, long long id, Logic* lb = nullptr):
            lb(lb), id(id), name(std::move(name)) {}

        explicit TermImpl(CType cType, Logic* lb = nullptr):
            lb(lb), id(getNextId(lb)), name(std::to_string(id)), c_type(cType) {}

        explicit TermImpl(std::string name, CType cType, Logic* lb = nullptr,
                          short bv_size = 0):
            lb(lb),
            id(getNextId(lb)), name(std::move(name)), bv_size(bv_size), c_type(cType) {}

        explicit TermImpl(std::string name, long long id, CType cType,
                          Logic* lb = nullptr):
            lb(lb),
            id(id), name(std::move(name)), c_type(cType) {}

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

    public:
        static long long getNextId(Logic* lb = nullptr) {
            if (lb == nullptr) {
                return gid++;
            } else {
                return lb->getNextId();
            }
        }
        [[nodiscard]] static std::string getStrRep(OpType opType);

        void print(std::ostream& os) const;
        void prettyPrint(std::ostream& os, int depth = 0) const;

        [[nodiscard]] long long getID() const { return id; }

        [[nodiscard]] const std::string& getName() const { return name; }

        [[nodiscard]] OpType getOpType() const { return opType; }

        [[nodiscard]] CType getCType() const { return c_type; }

        [[nodiscard]] const std::vector<LogicTerm>& getNodes() const { return nodes; }

        [[nodiscard]] bool getBoolValue() const;

        [[nodiscard]] int getIntValue() const;

        [[nodiscard]] double getFloatValue() const;

        [[nodiscard]] unsigned long long getBitVectorValue() const;

        [[nodiscard]] short getBitVectorSize() const;

        [[nodiscard]] std::string getValue() const;

        [[nodiscard]] unsigned long long getDepth() const { return depth; }

        [[nodiscard]] bool deepEquals(const TermImpl& other) const;

        [[nodiscard]] Logic* getLogic() const { return lb; }

        static long long gid;
        static long long getGID() { return gid; }

        static void reset() { gid = 0; }
    };
};     // namespace logicbase
#endif // TermImpl_HPP
