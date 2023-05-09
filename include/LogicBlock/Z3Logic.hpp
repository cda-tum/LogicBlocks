#ifndef CLIFFORDSATOPT_Z3LOGIC_H
#define CLIFFORDSATOPT_Z3LOGIC_H
#include "LogicBlock.hpp"

#include <functional>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include <z3++.h>
#include <z3_api.h>

namespace z3logic {

    using namespace logicbase;

    class Z3Base {
    protected:
        std::unordered_map<uint64_t, std::vector<std::pair<bool, z3::expr>>> variables;
        std::unordered_map<LogicTerm, std::vector<std::pair<bool, z3::expr>>, TermHash,
                           TermHash>
                                     cache{};
        std::shared_ptr<z3::context> ctx;

        bool producedInstance = false;

    public:
        explicit Z3Base(std::shared_ptr<z3::context> context):
            ctx(context) {}
        virtual ~Z3Base() = default;

        z3::expr     convert(const LogicTerm& a, CType toType = CType::ERRORTYPE);
        z3::context& getContext() { return *ctx; }

        static z3::expr getExprTerm(uint64_t id, CType type, Z3Base* z3base);

        z3::expr convertVariableTo(const LogicTerm& a, CType toType);
        z3::expr convertVariableFromBoolTo(const LogicTerm& a, CType toType);
        z3::expr convertVariableFromIntTo(const LogicTerm& a, CType toType);
        z3::expr convertVariableFromRealTo(const LogicTerm& a, CType toType);
        z3::expr convertVariableFromBitvectorTo(const LogicTerm& a, CType toType);

        z3::expr convertOperator(const LogicTerm& a, const LogicTerm& b,
                                 z3::expr (*op)(const z3::expr&, const z3::expr&),
                                 CType toType);
        z3::expr convertOperator(const LogicTerm& a, z3::expr (*op)(const z3::expr&),
                                 CType            toType);
        z3::expr convertOperator(const LogicTerm& a, const LogicTerm& b,
                                 const LogicTerm& c,
                                 z3::expr (*op)(const z3::expr&, const z3::expr&,
                                                const z3::expr&),
                                 CType toType);
        z3::expr convertOperator(const std::vector<LogicTerm>& terms,
                                 z3::expr (*op)(const z3::expr&, const z3::expr&),
                                 CType toType);

        z3::expr convertConstant(const LogicTerm& a, CType toType);
    };

    class Z3LogicBlock: public LogicBlock, public Z3Base {
    protected:
        std::shared_ptr<z3::solver> solver;
        void                        internalReset() override;

    public:
        Z3LogicBlock(std::shared_ptr<z3::context> context, std::shared_ptr<z3::solver> sol, bool convert = true):
            LogicBlock(convert), Z3Base(context), solver(sol) {}
        ~Z3LogicBlock() override {
            variables.clear();
            cache.clear();
        }
        void        assertFormula(const LogicTerm& a) override;
        void        produceInstance() override;
        Result      solve() override;
        void        dumpZ3State(std::ostream& stream);
        std::string dumpInternalSolver() override {
            std::stringstream ss;
            ss << (*solver);
            try {
                ctx->check_error();
            } catch (const z3::exception& e) {
                std::cerr << "Z3 reported an exception while trying to dump the internal state: " << e.msg() << std::endl;
            }
            return ss.str();
        }
    };

    class Z3LogicOptimizer: public LogicBlockOptimizer, public Z3Base {
    private:
        std::shared_ptr<z3::optimize> optimizer;
        void                          internalReset() override;

    public:
        Z3LogicOptimizer(std::shared_ptr<z3::context> context, std::shared_ptr<z3::optimize> opt,
                         bool convert = true):
            LogicBlockOptimizer(convert),
            Z3Base(context),
            optimizer(opt) {}
        ~Z3LogicOptimizer() override {
            variables.clear();
            cache.clear();
        }
        void   assertFormula(const LogicTerm& a) override;
        void   produceInstance() override;
        Result solve() override;
        void   dumpZ3State(std::ostream& stream);

        bool        makeMinimize() override;
        bool        makeMaximize() override;
        bool        maximize(const LogicTerm& term) override;
        bool        minimize(const LogicTerm& term) override;
        std::string dumpInternalSolver() override {
            std::stringstream ss;
            ss << (*optimizer);
            try {
                ctx->check_error();
            } catch (const z3::exception& e) {
                std::cerr << "Z3 reported an exception while trying to dump the internal state: " << e.msg() << std::endl;
            }
            return ss.str();
        }
    };

} // namespace z3logic
#endif // CLIFFORDSATOPT_Z3LOGIC_H
