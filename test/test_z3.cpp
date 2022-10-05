
#include "Encodings/Encodings.hpp"
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
TEST(TestZ3, ConstructDestruct) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, false);

    LogicTerm t = LogicTerm("x", CType::BOOL);
    LogicTerm b = t;
}

TEST(TestZ3, TestPrint) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, false);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::REAL);
    LogicTerm d = z3logic->makeVariable("d", CType::BITVECTOR, 8);

    LogicTerm t = a && (b == LogicTerm(1));
    t.print(std::cout);
    t.prettyPrint(std::cout);

    LogicTerm f = (c == LogicTerm(1.0)) && (d == LogicTerm(1, 8));
    f.print(std::cout);
    f.prettyPrint(std::cout);
}

TEST(TestZ3, SimpleTrue) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    z3logic::Z3LogicBlock z3logic(ctx, solver, true);

    LogicTerm a = z3logic.makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic.makeVariable("b", CType::BOOL);
    LogicTerm c = z3logic.makeVariable("c", CType::BOOL);

    z3logic.assertFormula(a && b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);
    EXPECT_EQ(a.getMaxChildrenDepth(), 1);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a || b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a == b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a != b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a && !b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!a || !b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(LogicTerm::implies(a, b));
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);
    c = z3logic.makeVariable("c", CType::BOOL);

    z3logic.assertFormula(a && b && c);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a           = z3logic.makeVariable("a", CType::BOOL);
    b           = z3logic.makeVariable("b", CType::BOOL);
    c           = z3logic.makeVariable("c", CType::BOOL);
    LogicTerm d = z3logic.makeVariable("d", CType::BOOL);

    z3logic.assertFormula((a && b) || (c && d));
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();
}

TEST(TestZ3, SimpleFalse) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    z3logic::Z3LogicBlock z3logic(ctx, solver, false);

    LogicTerm a = z3logic.makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!a);
    z3logic.assertFormula(a);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!b);
    z3logic.assertFormula(b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!a);
    z3logic.assertFormula(b);
    z3logic.assertFormula(a == b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a);
    z3logic.assertFormula(!b);
    z3logic.assertFormula(a == b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!a);
    z3logic.assertFormula(b);
    z3logic.assertFormula(a == b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a);
    z3logic.assertFormula(b);
    z3logic.assertFormula(a != b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!a);
    z3logic.assertFormula(!b);
    z3logic.assertFormula(a != b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(!a);
    z3logic.assertFormula(!b);
    z3logic.assertFormula(a && !b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a);
    z3logic.assertFormula(b);
    z3logic.assertFormula(a && !b);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::BOOL);
    b = z3logic.makeVariable("b", CType::BOOL);

    z3logic.assertFormula(a);
    z3logic.assertFormula(!b);
    z3logic.assertFormula(LogicTerm::implies(a, b));
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::UNSAT);

    z3logic.reset();
}

TEST(TestZ3, IntBase) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    z3logic::Z3LogicBlock z3logic(ctx, solver, false);

    LogicTerm a = z3logic.makeVariable("a", CType::INT);
    LogicTerm b = z3logic.makeVariable("b", CType::INT);
    LogicTerm c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a + b == c);
    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a - b == c);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a * b == c);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a / b == c);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);

    z3logic.assertFormula(a > b);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a < c);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);

    z3logic.assertFormula(a >= b);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a <= c);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
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

    z3logic.assertFormula(a == LogicTerm(3));
    z3logic.assertFormula(b == LogicTerm(2));
    z3logic.assertFormula(c == LogicTerm(1));
    z3logic.assertFormula(a - b == c);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a == LogicTerm(3));
    z3logic.assertFormula(b == LogicTerm(2));
    z3logic.assertFormula(c == LogicTerm(1));
    z3logic.assertFormula(c + b == a);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a == LogicTerm(3));
    z3logic.assertFormula(b == LogicTerm(2));
    z3logic.assertFormula(c == LogicTerm(1));
    z3logic.assertFormula((a > b) == LogicTerm(true));
    z3logic.assertFormula((b > c) == LogicTerm(true));

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a == LogicTerm(3));
    z3logic.assertFormula(b == LogicTerm(2));
    z3logic.assertFormula(c == LogicTerm(1));
    z3logic.assertFormula((c < a) == LogicTerm(true));
    z3logic.assertFormula((a < LogicTerm(4)) == LogicTerm(true));

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    LogicTerm bool_a = z3logic.makeVariable("bool_a", CType::BOOL);

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a == LogicTerm(3));
    z3logic.assertFormula(b == LogicTerm(2));
    z3logic.assertFormula(c == LogicTerm(1));
    z3logic.assertFormula(LogicTerm::ite(bool_a, a, b) == a);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();

    bool_a = z3logic.makeVariable("bool_a", CType::BOOL);

    a = z3logic.makeVariable("a", CType::INT);
    b = z3logic.makeVariable("b", CType::INT);
    c = z3logic.makeVariable("c", CType::INT);

    z3logic.assertFormula(a == LogicTerm(3));
    z3logic.assertFormula(b == LogicTerm(2));
    z3logic.assertFormula(c == LogicTerm(1));
    z3logic.assertFormula(LogicTerm::ite(bool_a, a, b) == b);

    z3logic.produceInstance();
    z3logic.dumpAll(std::cout);
    z3logic.dumpZ3State(std::cout);

    EXPECT_EQ(z3logic.solve(), Result::SAT);

    z3logic.reset();
}

TEST(TestZ3, AMOAndExactlyOneNaive) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, false);

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

    z3logic.reset();
}

TEST(TestZ3, AMOAndExactlyOneCMDR) {
    using namespace logicbase;
    using namespace encodings;

    int n = 22;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, false);

    std::vector<std::vector<LogicTerm>> a_nodes;

    for (int i = 0; i < n; ++i) {
        a_nodes.emplace_back();
        for (int j = 0; j < n; ++j) {
            a_nodes.back().emplace_back(z3logic->makeVariable("a_" + std::to_string(i) + "_" + std::to_string(j), CType::BOOL));
        }
    }

    for (int i = 0; i < n; ++i) {
        std::vector<LogicTerm> a_;
        for (int j = 0; j < n; ++j) {
            a_.emplace_back(a_nodes[i][j]);
        }
        LogicTerm aa = encodings::exactlyOneCmdr(groupVars(a_, n / 2), LogicTerm::noneTerm(), z3logic.get());
        z3logic->assertFormula(aa);
    }
    for (int i = 0; i < n; ++i) {
        std::vector<LogicTerm> a_;
        for (int j = 0; j < n; ++j) {
            a_.emplace_back(a_nodes[i][j]);
        }
        LogicTerm aa = atMostOneCmdr(groupVars(a_, 3), LogicTerm::noneTerm(), z3logic.get());
        z3logic->assertFormula(aa);
    }

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic.reset();
}

TEST(TestZ3, AMOAndExactlyOneBimander) {
    using namespace logicbase;
    using namespace encodings;

    int n = 11;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, false);

    std::vector<std::vector<LogicTerm>> a_nodes;

    for (int i = 0; i < n; ++i) {
        a_nodes.emplace_back();
        for (int j = 0; j < n; ++j) {
            a_nodes.back().emplace_back(z3logic->makeVariable("a_" + std::to_string(i) + "_" + std::to_string(j), CType::BOOL));
        }
    }

    for (int i = 0; i < n; ++i) {
        std::vector<LogicTerm> a_;
        for (int j = 0; j < n; ++j) {
            a_.emplace_back(a_nodes[i][j]);
        }
        LogicTerm aa = exactlyOneCmdr(groupVars(a_, 3), LogicTerm::noneTerm(), z3logic.get());
        z3logic->assertFormula(aa);
    }
    for (int i = 0; i < n; ++i) {
        std::vector<LogicTerm> a_;
        for (int j = 0; j < n; ++j) {
            a_.emplace_back(a_nodes[i][j]);
        }
        LogicTerm aa = atMostOneBiMander(a_, z3logic.get());
        z3logic->assertFormula(aa);
    }

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic.reset();
}

TEST(TestZ3, BuildBDDTest) {
    using namespace logicbase;
    using namespace encodings;

    int n = 23;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, false);

    std::vector<std::vector<LogicTerm>> a_nodes;

    for (int i = 0; i < n; ++i) {
        a_nodes.emplace_back();
        for (int j = 0; j < n; ++j) {
            a_nodes.back().emplace_back(z3logic->makeVariable("a_" + std::to_string(i) + "_" + std::to_string(j), CType::BOOL));
        }
    }

    for (int i = 0; i < n; ++i) {
        std::set<WeightedVar> a_;
        for (int j = 0; j < n; ++j) {
            a_.insert(WeightedVar(a_nodes[i][j], i + j));
        }
        LogicTerm aa = BuildBDD(a_, a_nodes[i], n, z3logic.get());
        z3logic->assertFormula(aa);
    }

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);

    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic.reset();
}
TEST(TestZ3, TestBasicModel) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, false);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::REAL);
    LogicTerm d = z3logic->makeVariable("d", CType::BITVECTOR, 8);

    z3logic->assertFormula(a);
    z3logic->assertFormula(b == LogicTerm(1));
    z3logic->assertFormula(c == LogicTerm(1.0));
    z3logic->assertFormula(d == LogicTerm(1, 8));

    z3logic->produceInstance();
    z3logic->dumpZ3State(std::cout);
    EXPECT_EQ(z3logic->solve(), Result::SAT);

    Model* model = z3logic->getModel();

    EXPECT_EQ(model->getBoolValue(a, z3logic.get()), true);
    EXPECT_EQ(model->getIntValue(b, z3logic.get()), 1);
    EXPECT_EQ(model->getRealValue(c, z3logic.get()), 1.0);
    EXPECT_EQ(model->getBitvectorValue(d, z3logic.get()), 1);

    model->getValue(a, z3logic.get());
    model->getValue(b, z3logic.get());
    model->getValue(c, z3logic.get());
    model->getValue(d, z3logic.get());

    z3logic.reset();
}

TEST(TestZ3, TestVariableConversionsToBool) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, true);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::REAL);
    LogicTerm d = z3logic->makeVariable("d", CType::BITVECTOR, 32);

    z3logic->assertFormula(a);
    z3logic->assertFormula(b);
    z3logic->assertFormula(c);
    z3logic->assertFormula(d);

    z3logic->dumpZ3State(std::cout);
    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic.reset();
}

TEST(TestZ3, TestVariableConversionsToBV) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, true);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::REAL);
    LogicTerm d = z3logic->makeVariable("d", CType::BITVECTOR, 32);

    z3logic->assertFormula(LogicTerm::bvAnd(d, a) == d);
    z3logic->assertFormula(LogicTerm::eq(d, a) == d);
    z3logic->assertFormula(LogicTerm::bvOr(d, b) == d);
    z3logic->assertFormula(LogicTerm::bvXor(d, b) == d);

    z3logic->dumpZ3State(std::cout);
    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic.reset();
}

TEST(TestZ3, TestVariableConversionsToInt) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, true);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::REAL);
    LogicTerm d = z3logic->makeVariable("d", CType::BITVECTOR, 32);

    z3logic->assertFormula(LogicTerm::bvAnd(d, a) == d);
    z3logic->assertFormula(LogicTerm::bvOr(d, b) == d);
    z3logic->assertFormula(LogicTerm::bvXor(d, b) == d);

    z3logic->dumpZ3State(std::cout);
    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic.reset();
}

TEST(TestZ3, TestVariableConversionsToReal) {
    using namespace logicbase;

    z3::context ctx{};
    z3::solver  solver{ctx};

    std::unique_ptr<z3logic::Z3LogicBlock> z3logic = std::make_unique<z3logic::Z3LogicBlock>(ctx, solver, true);

    LogicTerm a = z3logic->makeVariable("a", CType::BOOL);
    LogicTerm b = z3logic->makeVariable("b", CType::INT);
    LogicTerm c = z3logic->makeVariable("c", CType::REAL);
    LogicTerm d = z3logic->makeVariable("d", CType::BITVECTOR, 32);

    z3logic->assertFormula(LogicTerm::bvAnd(d, a) == d);
    z3logic->assertFormula(LogicTerm::bvOr(d, b) == d);
    z3logic->assertFormula(LogicTerm::bvXor(d, b) == d);

    z3logic->dumpZ3State(std::cout);
    EXPECT_EQ(z3logic->solve(), Result::SAT);

    z3logic.reset();
}
