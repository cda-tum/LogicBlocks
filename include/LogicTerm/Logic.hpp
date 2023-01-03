#ifndef LOGICBLOCK_LOGIC_H
#define LOGICBLOCK_LOGIC_H

#include <cassert>
#include <cstdarg>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <ostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

namespace logicbase {

    inline bool hasZ3() {
#ifdef Z3_FOUND
        return true;
#else
        return false;
#endif
    }

    enum class Result { SAT,
                        UNSAT,
                        NDEF };
    enum class OpType {
        None,
        Constant,
        Variable,
        EQ,
        XOR,
        AND,
        OR,
        ITE,
        NEG,
        IMPL,
        ADD,
        SUB,
        MUL,
        DIV,
        GT,
        LT,
        GTE,
        LTE,
        CALL,
        GET,
        SET,
        BitAnd,
        BitOr,
        BitEq,
        BitXor
    };

    enum class TermType { BASE,
                          CNF };

    enum class CType {
        BOOL,
        INT,
        REAL,
        BITVECTOR,
        FUNCTION,
        ARRAY,
        SET,
        ERRORTYPE
    };

    [[maybe_unused]] static Result resultFromString(const std::string& result) {
        if (result == "sat") {
            return Result::SAT;
        }
        if (result == "unsat") {
            return Result::UNSAT;
        }
        return Result::NDEF;
    }

    inline std::string toString(Result result) {
        switch (result) {
            case Result::SAT:
                return "SAT";
            case Result::UNSAT:
                return "UNSAT";
            case Result::NDEF:
            default:
                return "NDEF";
        }
    }

    inline std::string toString(OpType opType) {
        switch (opType) {
            case OpType::Variable:
                return "Variable";
            case OpType::Constant:
                return "Constant";
            case OpType::EQ:
                return "EQ";
            case OpType::XOR:
                return "XOR";
            case OpType::AND:
                return "AND";
            case OpType::OR:
                return "OR";
            case OpType::ITE:
                return "ITE";
            case OpType::NEG:
                return "NEG";
            case OpType::IMPL:
                return "IMPL";
            case OpType::ADD:
                return "ADD";
            case OpType::SUB:
                return "SUB";
            case OpType::MUL:
                return "MUL";
            case OpType::DIV:
                return "DIV";
            case OpType::GT:
                return "GT";
            case OpType::LT:
                return "LT";
            case OpType::GTE:
                return "GTE";
            case OpType::LTE:
                return "LTE";
            case OpType::BitAnd:
                return "BIT_AND";
            case OpType::BitOr:
                return "BIT_OR";
            case OpType::BitEq:
                return "BIT_EQ";
            case OpType::BitXor:
                return "BIT_XOR";
            case OpType::CALL:
                return "CALL";
            case OpType::GET:
                return "GET";
            case OpType::SET:
                return "SET";
            default:
                return "Unknown";
        }
    }

    inline std::string toString(CType ctype) {
        switch (ctype) {
            case CType::BOOL:
                return "B";
            case CType::BITVECTOR:
                return "BV";
            case CType::INT:
                return "I";
            case CType::REAL:
                return "F";
            case CType::FUNCTION:
                return "F(...)";
            case CType::ARRAY:
                return "A[...]";
            case CType::SET:
                return "S{...}";
            case CType::ERRORTYPE:
                throw std::runtime_error("Error: Unknown CType");
        }
        return "Error";
    }
    inline CType cTypeFromString(const std::string& ctype) {
        if (ctype == "B") {
            return CType::BOOL;
        }
        if (ctype == "BV") {
            return CType::BITVECTOR;
        }
        if (ctype == "I") {
            return CType::INT;
        }
        if (ctype == "F") {
            return CType::REAL;
        }
        if (ctype == "F(...)") {
            return CType::FUNCTION;
        }
        if (ctype == "A[...]") {
            return CType::ARRAY;
        }
        if (ctype == "S{...}") {
            return CType::SET;
        }
        return CType::BOOL;
    }

    inline bool isArith(OpType optype) {
        switch (optype) {
            case OpType::ADD:
            case OpType::SUB:
            case OpType::MUL:
            case OpType::DIV:
            case OpType::GT:
            case OpType::LT:
                return true;
            default:
                return false;
        }
    }

    inline bool isNumber(CType ctype) {
        switch (ctype) {
            case CType::INT:
            case CType::REAL:
            case CType::BITVECTOR:
                return true;
            default:
                return false;
        }
    }

    inline bool isCommutative(OpType op) {
        switch (op) {
            case OpType::ADD:
            case OpType::MUL:
            case OpType::EQ:
            case OpType::XOR:
            case OpType::AND:
            case OpType::OR:
                return true;
            default:
                return false;
        }
    }

    inline bool isAssociative(OpType op) {
        switch (op) {
            case OpType::ADD:
            case OpType::MUL:
            case OpType::EQ:
            case OpType::XOR:
            case OpType::AND:
            case OpType::OR:
                return true;
            default:
                return false;
        }
    }
    inline bool hasNeutralElement(OpType op) {
        switch (op) {
            case OpType::ADD:
            case OpType::MUL:
            case OpType::AND:
            case OpType::OR:
                return true;
            default:
                return false;
        }
    }

    inline CType getCType(OpType op) {
        switch (op) {
            case OpType::NEG:
            case OpType::IMPL:
            case OpType::AND:
            case OpType::OR:
            case OpType::GT:
            case OpType::LT:
            case OpType::GTE:
            case OpType::LTE:
                return CType::BOOL;
            case OpType::ADD:
            case OpType::SUB:
            case OpType::MUL:
            case OpType::DIV:
                return CType::INT;
            case OpType::ITE:
                return CType::BOOL;
            case OpType::BitAnd:
            case OpType::BitOr:
            case OpType::BitEq:
            case OpType::BitXor:
                return CType::BITVECTOR;
            default:
                return CType::BOOL;
        }
    }

    class TermImpl;
    class LogicTerm;

    using LogicVector   = std::vector<LogicTerm>;
    using LogicMatrix   = std::vector<LogicVector>;
    using LogicMatrix3D = std::vector<LogicMatrix>;
    using LogicMatrix4D = std::vector<LogicMatrix3D>;

    class Logic {
    public:
        virtual ~Logic()             = default;
        virtual uint64_t getNextId() = 0;
        virtual uint64_t getId()     = 0;
    };

    class TermInterface {
    public:
        virtual ~TermInterface()                                                                         = default;
        [[nodiscard]] virtual uint64_t                      getID() const                                = 0;
        [[nodiscard]] virtual const std::vector<LogicTerm>& getNodes() const                             = 0;
        [[nodiscard]] virtual OpType                        getOpType() const                            = 0;
        [[nodiscard]] virtual CType                         getCType() const                             = 0;
        [[nodiscard]] virtual bool                          getBoolValue() const                         = 0;
        [[nodiscard]] virtual int                           getIntValue() const                          = 0;
        [[nodiscard]] virtual double                        getFloatValue() const                        = 0;
        [[nodiscard]] virtual uint64_t                      getBitVectorValue() const                    = 0;
        [[nodiscard]] virtual int16_t                       getBitVectorSize() const                     = 0;
        [[nodiscard]] virtual const std::string&            getName() const                              = 0;
        [[nodiscard]] virtual std::string                   getConstantValue() const                     = 0;
        [[nodiscard]] virtual Logic*                        getLogic() const                             = 0;
        [[nodiscard]] virtual std::shared_ptr<TermImpl>     getImplementation() const                    = 0;
        [[nodiscard]] virtual bool                          deepEquals(const TermInterface& other) const = 0;
        virtual void                                        print(std::ostream& os) const                = 0;
        [[nodiscard]] virtual uint64_t                      getDepth() const                             = 0;
        [[nodiscard]] virtual uint64_t                      getMaxChildrenDepth() const                  = 0;
    };

    struct TermHash {
        std::size_t operator()(const TermInterface& t) const {
            if (t.getOpType() == OpType::None) {
                throw std::runtime_error("Invalid OpType");
            }
            return t.getID();
        }
        bool operator()(const TermInterface& t1, const TermInterface& t2) const {
            if (t1.getOpType() == OpType::None || t2.getOpType() == OpType::None) {
                throw std::runtime_error("Invalid OpType");
            }
            if (t1.getOpType() == OpType::Constant &&
                t2.getOpType() == OpType::Constant && t1.getCType() == t2.getCType()) {
                switch (t1.getCType()) {
                    case CType::BOOL:
                        return t1.getBoolValue() == t2.getBoolValue();
                    case CType::INT:
                        return t1.getIntValue() == t2.getIntValue();
                    case CType::REAL:
                        return t1.getFloatValue() == t2.getFloatValue();
                    case CType::BITVECTOR:
                        return t1.getBitVectorValue() == t2.getBitVectorValue();
                    default:
                        return false;
                }
            } else {
                return t1.getID() == t2.getID();
            }
        }
    };
    struct TermDepthComparator {
        bool operator()(const TermInterface& t1, const TermInterface& t2) const {
            if (t1.getOpType() == OpType::None || t2.getOpType() == OpType::None) {
                throw std::runtime_error("Invalid OpType");
            }
            if ((t1.getOpType() == OpType::Variable &&
                 t2.getOpType() == OpType::Variable) ||
                (t1.getOpType() == OpType::Constant &&
                 t2.getOpType() == OpType::Constant) ||
                t1.getDepth() == t2.getDepth()) {
                return t1.getID() > t2.getID();
            }
            {
                return t1.getDepth() > t2.getDepth();
            }
        }
    };

    struct Unorderedint64THash {
        std::size_t operator()(const std::unordered_set<int64_t>& t) const {
            std::size_t result{};
            for (const auto& item: t) {
                result += std::numeric_limits<uint64_t>::max() * static_cast<std::size_t>(item);
            }
            return result;
        }
        bool operator()(const std::unordered_set<int64_t>& t1, const std::unordered_set<int64_t>& t2) const {
            return t1 == t2;
        }
    };

    class LogicBlock;
    class Model;

} // namespace logicbase
#endif // LOGICBLOCK_LOGIC_H
