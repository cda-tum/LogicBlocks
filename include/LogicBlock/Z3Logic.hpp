//
// Created by Sarah on 08.07.2021.
//

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
        std::map<unsigned long long, std::vector<std::pair<bool, z3::expr>>> variables;
        std::unordered_map<LogicTerm, std::vector<std::pair<bool, z3::expr>>, TermHash,
                           TermHash>
                     cache{};
        z3::context& ctx;

        bool producedInstance = false;

    public:
        explicit Z3Base(z3::context& ctx):
            ctx(ctx) {}
        virtual ~Z3Base() = default;

        z3::expr     convert(const LogicTerm& a, CType to_type = CType::ERRORTYPE);
        z3::context& getContext() { return ctx; }

        static z3::expr getExprTerm(unsigned long long id, CType type, Z3Base* z3base);

        z3::expr convertVariableTo(const LogicTerm& a, CType to_type);
        z3::expr convertVariableFromBoolTo(const LogicTerm& a, CType to_type);
        z3::expr convertVariableFromIntTo(const LogicTerm& a, CType to_type);
        z3::expr convertVariableFromRealTo(const LogicTerm& a, CType to_type);
        z3::expr convertVariableFromBitvectorTo(const LogicTerm& a, CType to_type);

        z3::expr convertOperator(const LogicTerm& a, const LogicTerm& b,
                                 z3::expr (*op)(const z3::expr&, const z3::expr&),
                                 CType to_type);
        z3::expr convertOperator(const LogicTerm& a, z3::expr (*op)(const z3::expr&),
                                 CType            to_type);
        z3::expr convertOperator(const LogicTerm& a, const LogicTerm& b,
                                 const LogicTerm& c,
                                 z3::expr (*op)(const z3::expr&, const z3::expr&,
                                                const z3::expr&),
                                 CType to_type);
        z3::expr convertOperator(std::vector<LogicTerm> terms,
                                 z3::expr (*op)(const z3::expr&, const z3::expr&),
                                 CType to_type);

        z3::expr convertConstant(const LogicTerm& a, CType to_type);
    };

    class Z3LogicBlock: public LogicBlock, public Z3Base {
    protected:
        std::map<unsigned long long, std::vector<std::pair<bool, z3::expr>>> variables;
        z3::solver&                                                          solver;
        void                                                                 internal_reset() override;

    public:
        Z3LogicBlock(z3::context& ctx, z3::solver& solver, bool convertWhenAssert = true):
            LogicBlock(convertWhenAssert), Z3Base(ctx), solver(solver) {}
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
            ss << solver;
            try {
                ctx.check_error();
            } catch (const z3::exception& e) {
                std::cerr << "Z3 reported an exception while trying to dump the internal state: " << e.msg() << std::endl;
            }
            return ss.str();
        }
    };

    class Z3LogicOptimizer: public LogicBlockOptimizer, public Z3Base {
    private:
        std::map<unsigned long long, std::vector<std::pair<bool, z3::expr>>> variables;
        z3::optimize&                                                        optimizer;
        void                                                                 internal_reset() override;

    public:
        Z3LogicOptimizer(z3::context& ctx, z3::optimize& optimizer,
                         bool convertWhenAssert = true):
            LogicBlockOptimizer(convertWhenAssert),
            Z3Base(ctx),
            optimizer(optimizer) {}
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
            ss << optimizer;
            try {
                ctx.check_error();
            } catch (const z3::exception& e) {
                std::cerr << "Z3 reported an exception while trying to dump the internal state: " << e.msg() << std::endl;
            }
            return ss.str();
        }
    };

} // namespace z3logic
#endif // CLIFFORDSATOPT_Z3LOGIC_H
