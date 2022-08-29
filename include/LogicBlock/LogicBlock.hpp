#ifndef LOGICBLOCK_H
#define LOGICBLOCK_H

#include "LogicTerm/LogicTerm.hpp"
#include "Model.hpp"

#include <iostream>
#include <set>
#include <sys/types.h>
#include <vector>

namespace logicbase {
    class LogicBlock: public Logic {
    protected:
        std::set<LogicTerm, TermDepthComparator> clauses{};
        Model*                                   model{};
        bool                                     convertWhenAssert;
        virtual void                             internal_reset() = 0;
        unsigned long long                       gid              = 0U;

    public:
        explicit LogicBlock(bool convertWhenAssert = false):
            convertWhenAssert(convertWhenAssert) {}
        virtual ~LogicBlock() = default;

        unsigned long long getNextId() override { return gid++; };
        unsigned long long getId() override { return gid; };

        Model* getModel() { return model; }

        virtual void dump(const LogicTerm& a, std::ostream& stream) {
            a.prettyPrint(stream);
        }
        virtual void dumpAll(std::ostream& stream) {
            for (const LogicTerm& term: clauses) {
                dump(term, stream);
                stream << "  ";
            }
        }

        virtual void assertFormula(const LogicTerm& a) {
            if (a.getOpType() == OpType::AND) {
                for (const auto& clause: a.getNodes()) {
                    clauses.insert(clause);
                }
            } else {
                clauses.insert(a);
            }
        }

        LogicTerm makeVariable(const std::string& name, CType type = CType::BOOL,
                               short bv_size = 32) {
            if (type == CType::BITVECTOR && bv_size == 0) {
                throw std::invalid_argument("bv_size must be > 0");
            }
            return LogicTerm(name, type, this, bv_size);
        }

        virtual void   produceInstance() = 0;
        virtual Result solve()           = 0;
        virtual void   reset() {
            delete model;
            model = nullptr;
            clauses.clear();
            internal_reset();
            gid = 0U;
        };

        virtual std::string dumpInternalSolver() {
            return "";
        }
    };

    class LogicBlockOptimizer: public LogicBlock {
    protected:
        std::vector<std::pair<LogicTerm, double>> weightedTerms;

    public:
        explicit LogicBlockOptimizer(bool convertWhenAssert):
            LogicBlock(convertWhenAssert) {}
        void weightedTerm(const LogicTerm& a, double weight) {
            weightedTerms.emplace_back(a, weight);
        };
        void dumpAll(std::ostream& stream) override {
            for (const LogicTerm& term: clauses) {
                dump(term, stream);
                stream << std::endl;
                stream.flush();
            }
            for (const auto& it: weightedTerms) {
                dump(it.first, stream);
                stream << "(wt: " << it.second << ")" << std::endl;
                stream.flush();
            }
        }
        virtual bool makeMinimize()                  = 0;
        virtual bool makeMaximize()                  = 0;
        virtual bool maximize(const LogicTerm& term) = 0;
        virtual bool minimize(const LogicTerm& term) = 0;
        void         reset() override {
            model = nullptr;
            clauses.clear();
            weightedTerms.clear();
            internal_reset();
            gid = 0U;
        };
    };
} // namespace logicbase
#endif // LOGICBLOCK_H
