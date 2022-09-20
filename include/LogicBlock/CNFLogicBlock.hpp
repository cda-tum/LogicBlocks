//
// Created by Sarah on 30.05.2022.
//

#ifndef LOGICBLOCKS_CNFLOGICBLOCK_H
#define LOGICBLOCKS_CNFLOGICBLOCK_H

#include "LogicBlock.hpp"

#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>

namespace cnflogic {
    using namespace logicbase;

    class CNFLogicBlock: public LogicBlock {
    protected:
        std::ostream&                                                        out;
        std::unordered_set<std::unordered_set<int64_t>, Unorderedint64THash> convertedClauses{};
        std::unordered_map<uint64_t, int64_t>                                variables{};
        uint64_t                                                             varId = 0;
        LogicTerm                                                            trueTerm;
        LogicTerm                                                            falseTerm;
        void                                                                 internalReset() override;

    public:
        explicit CNFLogicBlock(bool convertWhenAssert = false, std::ostream& out = std::cout):
            LogicBlock(convertWhenAssert), out(out), varId(3) {
            trueTerm  = makeVariable("true", CType::BOOL);
            falseTerm = makeVariable("false", CType::BOOL);
            clauses.insert(trueTerm);
            clauses.insert(falseTerm);
            variables.insert(std::make_pair(trueTerm.getID(), 1));
            variables.insert(std::make_pair(falseTerm.getID(), 2));

            convertedClauses.insert({1});  //True Literal
            convertedClauses.insert({-2}); //False Literal
        }
        ~CNFLogicBlock() override = default;

        void   assertFormula(const LogicTerm& a) override;
        void   produceInstance() override;
        Result solve() override;

        void dump(const LogicTerm& a, std::ostream& stream) override;
        void dumpAll(std::ostream& stream) override;

        void                        convert();
        std::unordered_set<int64_t> convert(const LogicTerm& a);
        LogicTerm                   convertToCNF(const LogicTerm& a);

        void reset() override {
            delete model;
            model = nullptr;
            clauses.clear();
            internalReset();
            gid = 0;
        };
    };

} // namespace cnflogic

#endif //LOGICBLOCKS_CNFLOGICBLOCK_H
