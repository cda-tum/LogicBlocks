
#include "Encodings/Encodings.hpp"
#include "LogicBlock/SMTLibLogicBlock.hpp"
#include "LogicTerm/Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
class TestSMTLib: public testing::TestWithParam<logicbase::OpType> {
protected:
    void SetUp() override {
    }
};
TEST(TestSMTLib, ConstructDestruct) {
    using namespace logicbase;

    std::unique_ptr<smtliblogic::SMTLogicBlock> const smtLibLogic = std::make_unique<smtliblogic::SMTLogicBlock>(false, std::cout);
}

TEST(TestSMTLib, TestPrint) {
    using namespace logicbase;

    std::unique_ptr<smtliblogic::SMTLogicBlock> const smtLibLogic = std::make_unique<smtliblogic::SMTLogicBlock>(false, std::cout);

    LogicTerm a = smtLibLogic->makeVariable("a", CType::BOOL);
    LogicTerm b = smtLibLogic->makeVariable("b", CType::INT);
    LogicTerm c = smtLibLogic->makeVariable("c", CType::REAL);
    LogicTerm d = smtLibLogic->makeVariable("d", CType::BITVECTOR, 8);

    LogicTerm t = a && (b == LogicTerm(1));
    t.print(std::cout);
    t.prettyPrint(std::cout);

    LogicTerm f = (c == LogicTerm(1.0)) && (d == LogicTerm(1, 8));
    f.print(std::cout);
    f.prettyPrint(std::cout);

    smtLibLogic->assertFormula(t);
    smtLibLogic->assertFormula(f);

    smtLibLogic->setOutputLogic(smtliblogic::SMTLibLogic::QF_BV);
    smtLibLogic->produceInstance();
}
