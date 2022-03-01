#include <boost/log/trivial.hpp>
#include <boost/program_options.hpp>
#include <boost/program_options/value_semantic.hpp>
#include <iostream>

#include "Logic.hpp"
#include "Logic/LogicBlock/Z3Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"
#include "utils/util.hpp"

int main(int argc, char *argv[]) {
  namespace po = boost::program_options;
  po::options_description desc("Allowed options");

  z3logic::Z3LogicBlock z3logic(true);

  logicbase::LogicTerm a =
      z3logic.makeVariable("a", logicbase::CType::BITVECTOR, 5);
  logicbase::LogicTerm b =
      z3logic.makeVariable("b", logicbase::CType::BITVECTOR, 5);
  logicbase::LogicTerm c =
      z3logic.makeVariable("c", logicbase::CType::BITVECTOR, 5);
  z3logic.assertFormula((a && b) == c);
  z3logic.assertFormula(c == logicbase::LogicTerm(10, 5));
  z3logic.assertFormula(a != logicbase::LogicTerm(10, 5));
  z3logic.dumpAll(std::cout);
  z3logic.produceInstance();
  z3logic.dumpZ3State(std::cout);
  if (z3logic.solve() == logicbase::Result::SAT) {
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