#include "LogicBlock/Z3Logic.hpp"
#include "Encodings/Encodings.hpp"

#include <iostream>

using namespace logicbase;
int main() {
    z3::context ctx{};
    z3::solver  solver{ctx};

    z3logic::Z3LogicBlock z3logic(ctx, solver, true);

    LogicTerm a       = z3logic.makeVariable("a", CType::BITVECTOR, 5);
    LogicTerm b       = z3logic.makeVariable("b", CType::BITVECTOR, 5);
    LogicTerm c       = z3logic.makeVariable("c", CType::BITVECTOR, 5);
    LogicTerm d       = z3logic.makeVariable("d", CType::BITVECTOR, 5);
    LogicTerm e       = z3logic.makeVariable("e", CType::BITVECTOR, 5);
    LogicTerm f       = z3logic.makeVariable("f", CType::BITVECTOR, 5);
    LogicTerm g       = z3logic.makeVariable("g", CType::BITVECTOR, 5);
    LogicTerm changes = LogicTerm(true);
    changes           = changes && (a & b);
    changes           = changes && (c & d);
    changes           = changes && (e & (f & g));
    changes.print(std::cout);
    std::cout << std::endl;
    z3logic.assertFormula(changes);
    z3logic.dumpAll(std::cout);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);
    if (z3logic.solve() == Result::SAT) {
        std::cout << "SAT" << std::endl;
        std::cout << "a: ";
        z3logic.getModel()->getValue(a, &z3logic).print(std::cout);
        std::cout << std::endl;
        std::cout << "b: ";
        z3logic.getModel()->getValue(b, &z3logic).print(std::cout);
        std::cout << std::endl;
        std::cout << "c: ";
        z3logic.getModel()->getValue(c, &z3logic).print(std::cout);
        std::cout << std::endl;
    }

    LogicTerm aa = (a < LogicTerm(1));

    aa.print(std::cout);

    std::vector<LogicTerm> clauseVars;
    for (int i = 0; i < 5; ++i) {
        clauseVars.push_back(LogicTerm(i));
    }
    AtMostOneBiMander(clauseVars, &z3logic);
}
