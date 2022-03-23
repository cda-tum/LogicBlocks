//
// Created by Sarah on 08.07.2021.
//

#ifndef CLIFFORDSATOPT_Z3LOGIC_H
#define CLIFFORDSATOPT_Z3LOGIC_H
#include "LogicBlock.hpp"
#include "Z3Model.hpp"

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

    using namespace z3;
    using namespace logicbase;

    class Z3Base {
    protected:
        std::map<unsigned long long, std::vector<std::pair<bool, expr>>> variables;
        std::unordered_map<LogicTerm, std::vector<std::pair<bool, expr>>, TermHash,
                           TermHash>
                     cache{};
        z3::context& ctx;

    public:
        Z3Base(z3::context& ctx):
            ctx(ctx) {}
        virtual ~Z3Base() {}

        expr     convert(const LogicTerm& a, CType to_type = CType::ERRORTYPE);
        expr     getExprTerm(unsigned long long id, CType type);
        context& getContext() { return ctx; }

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
        solver& solver;
        void    internal_reset() override;

    public:
        Z3LogicBlock(context& ctx, z3::solver& solver, bool convertWhenAssert = true):
            LogicBlock(convertWhenAssert), Z3Base(ctx), solver(solver) {}
        ~Z3LogicBlock() { internal_reset(); }
        void   assertFormula(const LogicTerm& a) override;
        void   produceInstance() override;
        Result solve() override;
        void   dumpZ3State(std::ostream& stream);
    };

    class Z3LogicOptimizer: public LogicBlockOptimizer, public Z3Base {
    private:
        z3::optimize&                                                    optimizer;
        std::map<unsigned long long, std::vector<std::pair<bool, expr>>> variables;
        void                                                             internal_reset() override;

    public:
        Z3LogicOptimizer(context& ctx, z3::optimize& optimizer,
                         bool convertWhenAssert = true):
            LogicBlockOptimizer(convertWhenAssert),
            Z3Base(ctx),
            optimizer(optimizer) {}
        ~Z3LogicOptimizer() {}
        void   assertFormula(const LogicTerm& a) override;
        void   produceInstance() override;
        Result solve() override;
        void   dumpZ3State(std::ostream& stream);

        bool makeMinimize() override;
        bool makeMaximize() override;
        bool maximize(const LogicTerm& term) override;
        bool minimize(const LogicTerm& term) override;
    };

} // namespace z3logic
#endif // CLIFFORDSATOPT_Z3LOGIC_H
