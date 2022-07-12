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
}
