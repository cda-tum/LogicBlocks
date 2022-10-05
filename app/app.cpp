#include "LogicBlock/CNFLogicBlock.hpp"
#include "LogicBlock/SMTLibLogicBlock.hpp"
#include "LogicUtil/util_logicblock.hpp"
#include "utils/logging.hpp"

#include <chrono>
#include <iostream>

using namespace logicbase;
int main() {
    util::init("", plog::error);
    bool success = false;
    auto z3logic = logicutil::getZ3LogicBlock(success, true);
    if (!success) {
        ERROR() << "Z3 not found";
        return 1;
    }

    LogicTerm a       = z3logic->makeVariable("a", CType::BITVECTOR, 5);
    LogicTerm b       = z3logic->makeVariable("b", CType::BITVECTOR, 5);
    LogicTerm c       = z3logic->makeVariable("c", CType::BITVECTOR, 5);
    LogicTerm d       = z3logic->makeVariable("d", CType::BITVECTOR, 5);
    LogicTerm e       = z3logic->makeVariable("e", CType::BITVECTOR, 5);
    LogicTerm f       = z3logic->makeVariable("f", CType::BITVECTOR, 5);
    LogicTerm g       = z3logic->makeVariable("g", CType::BITVECTOR, 5);
    LogicTerm changes = LogicTerm(true);
    changes           = changes && (a & b);
    changes           = changes && (c & d);
    changes           = changes && (e & (f & g));
    changes.prettyPrint(std::cout);
    std::cout << std::endl;
    z3logic->assertFormula(changes);
    //        z3logic->dumpAll(std::cout);
    z3logic->produceInstance();
    //        if (z3logic.solve() == Result::SAT) {
    //            std::cout << "SAT" << std::endl;
    //            std::cout << "a: ";
    //            z3logic.getModel()->getValue(a, &z3logic).print(std::cout);
    //            std::cout << std::endl;
    //            std::cout << "b: ";
    //            z3logic.getModel()->getValue(b, &z3logic).print(std::cout);
    //            std::cout << std::endl;
    //            std::cout << "c: ";
    //            z3logic.getModel()->getValue(c, &z3logic).print(std::cout);
    //            std::cout << std::endl;
    //        }

    //        std::vector<std::vector<LogicTerm>> a_nodes;
    //
    //        auto totalStart = std::chrono::high_resolution_clock::now();
    //        int  n          = 20;
    //        for (int i = 0; i < n; ++i) {
    //            a_nodes.emplace_back();
    //            for (int j = 0; j < n; ++j) {
    //                a_nodes.back().emplace_back(z3logic->makeVariable("a_" + std::to_string(i) + "_" + std::to_string(j), CType::BOOL));
    //            }
    //        }
    //
    //        for (int i = 0; i < n; ++i) {
    //            LogicTerm a_ = LogicTerm(0);
    //            for (int j = 0; j < n; ++j) {
    //                a_ = a_ + LogicTerm::ite(a_nodes[i][j], LogicTerm(1), LogicTerm(0));
    //            }
    //            LogicTerm aa = (a_ <= LogicTerm(1));
    //            z3logic->assertFormula(aa);
    //        }
    //        for (int i = 0; i < n; ++i) {
    //            LogicTerm a_ = LogicTerm(0);
    //            for (int j = 0; j < n; ++j) {
    //                a_ = a_ + LogicTerm::ite(a_nodes[j][i], LogicTerm(1), LogicTerm(0));
    //            }
    //            LogicTerm aa = (a_ == LogicTerm(1));
    //            z3logic->assertFormula(aa);
    //        }
    //        auto                          totalEnd = std::chrono::high_resolution_clock::now();
    //        std::chrono::duration<double> diff     = totalEnd - totalStart;
    //        std::cout << "Time: " << diff.count() << std::endl;
    //

    //        z3logic.dumpAll(std::cout);
    //        z3logic.dumpZ3State(std::cout);
    //        if (z3logic.solve() == Result::SAT) {
    //            for (int i = 0; i < 4; ++i) {
    //                for (int j = 0; j < 4; ++j) {
    //                    std::cout << "a_" << i << "_" << j << ": ";
    //                    z3logic.getModel()->getValue(a_nodes[i][j], &z3logic).print(std::cout);
    //                    std::cout << std::endl;
    //                }
    //            }
    //        }
    //        smtliblogic::SMTLogicBlock smtLogicBlock(true, std::cout);
    //        smtLogicBlock.setOutputLogic(smtliblogic::SMTLibLogic::QF_UF);
    //        LogicTerm a = smtLogicBlock.makeVariable("a", CType::BOOL);
    //        LogicTerm b = smtLogicBlock.makeVariable("b", CType::BOOL);
    //        LogicTerm c = smtLogicBlock.makeVariable("c", CType::BOOL);
    //        LogicTerm d = smtLogicBlock.makeVariable("d", CType::BOOL);
    //        LogicTerm e = smtLogicBlock.makeVariable("e", CType::BOOL);
    //        LogicTerm f = smtLogicBlock.makeVariable("f", CType::BOOL);
    //        LogicTerm g = smtLogicBlock.makeVariable("g", CType::BOOL);
    //        LogicTerm h = smtLogicBlock.makeVariable("h", CType::BOOL);
    //        LogicTerm i = smtLogicBlock.makeVariable("i", CType::BOOL);
    //        LogicTerm j = smtLogicBlock.makeVariable("j", CType::BOOL);
    //        smtLogicBlock.assertFormula(a || b);
    //        smtLogicBlock.assertFormula(c && d);
    //        LogicTerm ch = c || (a == b);
    //        smtLogicBlock.assertFormula(ch);
    //            ch.prettyPrint(std::cout);
    //
    //        smtLogicBlock.produceInstance();
    //
    //    cnflogic::CNFLogicBlock cnfLogicBlock(true, std::cout);
    //    LogicTerm               a = cnfLogicBlock.makeVariable("a", CType::BOOL);
    //    LogicTerm               b = cnfLogicBlock.makeVariable("b", CType::BOOL);
    //    LogicTerm               c = cnfLogicBlock.makeVariable("c", CType::BOOL);
    //    LogicTerm               d = cnfLogicBlock.makeVariable("d", CType::BOOL);
    //
    //    LogicTerm changes = LogicTerm(true);
    //    changes           = (a != b);
    //    changes           = changes && (b != c);
    //    cnfLogicBlock.convertToCNF(changes).prettyPrint(std::cout);
    //    ERROR() << "TESTING";
}
