/*
 * This file is part of the MQT QMAP library which is released under the MIT license.
 * See file README.md or go to https://www.cda.cit.tum.de/research/ibm_qx_mapping/ for more information.
 */

#include "LogicTerm/Logic.hpp"
#include "LogicTerm/LogicTerm.hpp"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

class TestBaseGates: public testing::TestWithParam<logicbase::OpType> {
protected:
    void SetUp() override {
    }
};

TEST(TestBaseGates, VanishingConstant) {
    using namespace logicbase;
    LogicTerm result = LogicTerm(true) && LogicTerm(false);
    EXPECT_EQ(result.getBoolValue(), false);

    result = LogicTerm(true) || LogicTerm(false);
    EXPECT_EQ(result.getBoolValue(), true);

    result = LogicTerm(false) && LogicTerm(true);
    EXPECT_EQ(result.getBoolValue(), false);

    result = LogicTerm(false) || LogicTerm(true);
    EXPECT_EQ(result.getBoolValue(), true);

    result = LogicTerm(true) == LogicTerm(false);
    EXPECT_EQ(result.getBoolValue(), false);

    result = LogicTerm(true) != LogicTerm(false);
    EXPECT_EQ(result.getBoolValue(), true);

    result = LogicTerm::implies(LogicTerm(true), LogicTerm(false));
    EXPECT_EQ(result.getBoolValue(), false);

    result = LogicTerm::implies(LogicTerm(true), LogicTerm(true));
    EXPECT_EQ(result.getBoolValue(), true);

    result = LogicTerm::implies(LogicTerm(false), LogicTerm(false));
    EXPECT_EQ(result.getBoolValue(), true);
}
TEST(TestBaseGates, LeftOverVariable) {
    using namespace logicbase;
    LogicTerm variable = LogicTerm("x", CType::BOOL);
    LogicTerm result   = LogicTerm(true) && variable;
    EXPECT_EQ(result.getOpType(), OpType::Variable);

    result = variable || LogicTerm(false);
    EXPECT_EQ(result.getOpType(), OpType::Variable);

    result = LogicTerm(false) && variable;
    EXPECT_EQ(result.getBoolValue(), false);

    result = variable || LogicTerm(true);
    EXPECT_EQ(result.getBoolValue(), true);
}

TEST(TestBaseGates, NeutralElement) {
    using namespace logicbase;
    EXPECT_EQ(LogicTerm::getNeutralElement(OpType::AND).getBoolValue(), true);
    EXPECT_EQ(LogicTerm::getNeutralElement(OpType::OR).getBoolValue(), false);
    EXPECT_EQ(LogicTerm::getNeutralElement(OpType::ADD).getIntValue(), 0);
    EXPECT_EQ(LogicTerm::getNeutralElement(OpType::MUL).getIntValue(), 1);
}
