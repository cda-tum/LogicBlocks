
#include "LogicTerm/Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

class TestBaseInt: public testing::TestWithParam<logicbase::OpType> {
protected:
    void SetUp() override {
    }
};

TEST(TestBaseInt, VanishingConstant) {
    using namespace logicbase;
    LogicTerm result = LogicTerm(1) + LogicTerm(0);
    EXPECT_EQ(result.getIntValue(), 1);

    result = LogicTerm(2) + LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), 3);

    result = LogicTerm(2) - LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), 1);

    result = LogicTerm(2) * LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), 2);

    result = LogicTerm(2) * LogicTerm(2);
    EXPECT_EQ(result.getIntValue(), 4);

    result = LogicTerm(2) / LogicTerm(2);
    EXPECT_EQ(result.getIntValue(), 1);

    result = LogicTerm(2) > LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), true);

    result = LogicTerm(2) < LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), false);

    result = LogicTerm(2) >= LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), true);

    result = LogicTerm(2) <= LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), false);

    result = LogicTerm(2) == LogicTerm(1);
    EXPECT_EQ(result.getIntValue(), false);
}
TEST(TestBaseInt, LeftOverVariable) {
    using namespace logicbase;
    LogicTerm variable = LogicTerm("x", CType::INT);

    LogicTerm result = variable + LogicTerm(0);
    EXPECT_EQ(result.getName(), "x");

    result = variable + LogicTerm(0);
    EXPECT_EQ(result.getName(), "x");

    result = variable + LogicTerm(1);
    EXPECT_EQ(result.getMaxChildrenDepth(), 2);

    result = variable - LogicTerm(0);
    EXPECT_EQ(result.getName(), "x");

    result = variable - LogicTerm(1);
    EXPECT_EQ(result.getMaxChildrenDepth(), 2);

    result = variable * LogicTerm(1);
    EXPECT_EQ(result.getName(), "x");

    result = variable * LogicTerm(0);
    EXPECT_EQ(result.getIntValue(), 0);

    result = variable * LogicTerm(2);
    EXPECT_EQ(result.getMaxChildrenDepth(), 2);

    result = variable / LogicTerm(1);
    EXPECT_EQ(result.getName(), "x");

    result = variable / LogicTerm(2);
    EXPECT_EQ(result.getMaxChildrenDepth(), 2);
}
