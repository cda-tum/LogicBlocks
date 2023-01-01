
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

TEST(TestZ3Opt, SimpleTrue) {
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

    z3logic->reset();
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a || b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a == b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a != b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a && !b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();
    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(!a || !b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(LogicTerm::implies(a, b));
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();
    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();
    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);
    c = z3logic->makeVariable("c", CType::BOOL);

    z3logic->assertFormula(a && b && c);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic->reset();
}

TEST(TestZ3Opt, SimpleFalse) {
    using namespace logicbase;

    z3::context  ctx{};
    z3::optimize opt{ctx};

    std::unique_ptr<z3logic::Z3LogicOptimizer> z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(!a);
    z3logic->assertFormula(a);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(!b);
    z3logic->assertFormula(b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(!a);
    z3logic->assertFormula(b);
    z3logic->assertFormula(a == b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a);
    z3logic->assertFormula(!b);
    z3logic->assertFormula(a == b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(!a);
    z3logic->assertFormula(b);
    z3logic->assertFormula(a == b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a);
    z3logic->assertFormula(b);
    z3logic->assertFormula(a != b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(!a);
    z3logic->assertFormula(!b);
    z3logic->assertFormula(a != b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(!a);
    z3logic->assertFormula(!b);
    z3logic->assertFormula(a && !b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a);
    z3logic->assertFormula(b);
    z3logic->assertFormula(a && !b);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::BOOL);
    b = z3logic->makeVariable("b", CType::BOOL);

    z3logic->assertFormula(a);
    z3logic->assertFormula(!b);
    z3logic->assertFormula(LogicTerm::implies(a, b));
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::UNSAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();
}

TEST(TestZ3Opt, IntBase) {
    using namespace logicbase;

    z3::context  ctx{};
    z3::optimize opt{ctx};

    std::unique_ptr<z3logic::Z3LogicOptimizer> z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);

    LogicTerm a = z3logic->makeVariable("a", CType::INT);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a + b == c);
    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a - b == c);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a * b == c);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a / b == c);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);

    z3logic->assertFormula(a > b);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a < c);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);

    z3logic->assertFormula(a >= b);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a <= c);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();
}
TEST(TestZ3Opt, IntNumbers) {
    using namespace logicbase;

    z3::context  ctx{};
    z3::optimize opt{ctx};

    std::unique_ptr<z3logic::Z3LogicOptimizer> z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);

    LogicTerm a = z3logic->makeVariable("a", CType::INT);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a == LogicTerm(3));
    z3logic->assertFormula(b == LogicTerm(2));
    z3logic->assertFormula(c == LogicTerm(1));
    z3logic->assertFormula(a - b == c);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a == LogicTerm(3));
    z3logic->assertFormula(b == LogicTerm(2));
    z3logic->assertFormula(c == LogicTerm(1));
    z3logic->assertFormula(c + b == a);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a == LogicTerm(3));
    z3logic->assertFormula(b == LogicTerm(2));
    z3logic->assertFormula(c == LogicTerm(1));
    z3logic->assertFormula((a > b) == LogicTerm(true));
    z3logic->assertFormula((b > c) == LogicTerm(true));

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a == LogicTerm(3));
    z3logic->assertFormula(b == LogicTerm(2));
    z3logic->assertFormula(c == LogicTerm(1));
    z3logic->assertFormula((c < a) == LogicTerm(true));
    z3logic->assertFormula((a < LogicTerm(4)) == LogicTerm(true));

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    LogicTerm bool_a = z3logic->makeVariable("bool_a", CType::BOOL);

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a == LogicTerm(3));
    z3logic->assertFormula(b == LogicTerm(2));
    z3logic->assertFormula(c == LogicTerm(1));
    z3logic->assertFormula(LogicTerm::ite(bool_a, a, b) == a);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();

    bool_a = z3logic->makeVariable("bool_a", CType::BOOL);

    a = z3logic->makeVariable("a", CType::INT);
    b = z3logic->makeVariable("b", CType::INT);
    c = z3logic->makeVariable("c", CType::INT);

    z3logic->assertFormula(a == LogicTerm(3));
    z3logic->assertFormula(b == LogicTerm(2));
    z3logic->assertFormula(c == LogicTerm(1));
    z3logic->assertFormula(LogicTerm::ite(bool_a, a, b) == b);

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
    z3logic->reset();
}

TEST(TestZ3Opt, AMOAndExactlyOneNaive) {
    {
        using namespace logicbase;

        z3::context  ctx{};
        z3::optimize opt{ctx};

        std::unique_ptr<z3logic::Z3LogicOptimizer> z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);

        std::vector<std::vector<LogicTerm>> a_nodes;

        for (int i = 0; i < 4; ++i) {
            a_nodes.emplace_back();
            for (int j = 0; j < 4; ++j) {
                a_nodes.back().emplace_back(z3logic->makeVariable("a_" + std::to_string(i) + "_" + std::to_string(j), CType::BOOL));
            }
        }

        for (int i = 0; i < 4; ++i) {
            LogicTerm a_ = LogicTerm(0);
            for (int j = 0; j < 4; ++j) {
                a_ = a_ + LogicTerm::ite(a_nodes[i][j], LogicTerm(1), LogicTerm(0));
            }
            LogicTerm aa = (a_ <= LogicTerm(1));
            z3logic->assertFormula(aa);
        }
        for (int i = 0; i < 4; ++i) {
            LogicTerm a_ = LogicTerm(0);
            for (int j = 0; j < 4; ++j) {
                a_ = a_ + LogicTerm::ite(a_nodes[j][i], LogicTerm(1), LogicTerm(0));
            }
            LogicTerm aa = (a_ == LogicTerm(1));
            z3logic->assertFormula(aa);
        }

        z3logic->produceInstance();
        z3logic->dumpZ3State(std::cout);

        EXPECT_EQ(z3logic->solve(), Result::SAT);

        z3logic = std::make_unique<z3logic::Z3LogicOptimizer>(ctx, opt, false);
        z3logic->reset();
    }
}
