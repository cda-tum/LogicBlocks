#include <boost/log/trivial.hpp>
#include <boost/program_options.hpp>
#include <boost/program_options/value_semantic.hpp>

#include "Logic.hpp"
#include "Logic/LogicBlock/Z3Logic.hpp"
#include "utils/util.hpp"

int main(int argc, char *argv[]) {
  namespace po = boost::program_options;
  po::options_description desc("Allowed options");

  z3logic::Z3LogicBlock z3logic(true);

  logicbase::LogicTerm a =
      z3logic.makeVariable("a", logicbase::CType::BITVECTOR, 32);
  logicbase::LogicTerm b =
      z3logic.makeVariable("b", logicbase::CType::BITVECTOR, 32);
  logicbase::LogicTerm c =
      z3logic.makeVariable("c", logicbase::CType::BITVECTOR, 32);
  z3logic.assertFormula(a + b == c);
  z3logic.dumpAll(std::cout);
  z3logic.produceInstance();
  z3logic.solve();
  z3logic.getModel()->getResult();
}