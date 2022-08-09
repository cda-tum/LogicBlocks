
#include "LogicBlock/Z3Logic.hpp"
#include "LogicTerm/Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
class TestZ3: public testing::TestWithParam<logicbase::OpType> {
protected:
    void SetUp() override {
    }
};

TEST(TestZ3, SimpleTrue) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    z3logic::Z3LogicBlock z3logic(ctx, solver, false);

    LogicTerm a = z3logic.makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a && b);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a || b);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a == b);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a != b);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a && !b);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!a || !b);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();
}
TEST(TestZ3, IntNumbers) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    z3logic::Z3LogicBlock z3logic(ctx, solver, false);

    LogicTerm a = z3logic.makeVariable("a", CType::INT);
    LogicTerm b = z3logic.makeVariable("b", CType::INT);
    LogicTerm c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a + b == c);
    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a - b == c);

    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a * b == c);

    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();



    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a / b == c);

    z3logic.produceInstance();
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();


}
