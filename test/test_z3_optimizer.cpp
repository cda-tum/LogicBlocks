
#include "LogicBlock/Z3Logic.hpp"
#include "LogicTerm/Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
class TestZ3Opt: public testing::TestWithParam<logicbase::OpType> {
protected:
    void SetUp() override {
    }
};

TEST(TestZ3Opt, ConstructDestruct) {
    using namespace logicbase;

    z3::context  ctx{};
    z3::optimize opt{ctx};

    std::unique_ptr<z3logic::Z3LogicOptimizer> z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::BOOL);
    LogicTerm c = z3logic->makeVariable("c", CType::BOOL);

    z3logic->assertFormula(a && b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);
    std::stringstream ss{};
    ss << opt;

    z3logic->reset();
}
