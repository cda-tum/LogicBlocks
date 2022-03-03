#include <boost/log/trivial.hpp>
#include <boost/program_options.hpp>
#include <boost/program_options/value_semantic.hpp>
#include <iostream>
#include <z3++.h>

#include "Logic.hpp"
#include "Logic/LogicBlock/Z3Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"
#include "utils/util.hpp"

using namespace logicbase;
int main(int argc, char *argv[]) {
  namespace po = boost::program_options;
  po::options_description desc("Allowed options");

  z3::context ctx{};
  z3::solver solver{ctx};

  z3logic::Z3LogicBlock z3logic(ctx, solver, true);

  LogicTerm a = z3logic.makeVariable("a", CType::BITVECTOR, 5);
  LogicTerm b = z3logic.makeVariable("b", CType::BITVECTOR, 5);
  LogicTerm c = z3logic.makeVariable("c", CType::BITVECTOR, 5);
  LogicTerm d = z3logic.makeVariable("d", CType::BITVECTOR, 5);
  LogicTerm e = z3logic.makeVariable("e", CType::BITVECTOR, 5);
  LogicTerm f = z3logic.makeVariable("f", CType::BITVECTOR, 5);
  LogicTerm g = z3logic.makeVariable("g", CType::BITVECTOR, 5);
  LogicTerm changes = LogicTerm(true);
  changes = changes && (a & b);
  changes = changes && (c & d);
  changes = changes && (e & (f & g));
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
}