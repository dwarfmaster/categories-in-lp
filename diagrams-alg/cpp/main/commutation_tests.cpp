
#include <gtest/gtest.h>

TEST(TrivalTest, BasicAssertions) {
    EXPECT_STRNE("hello", "world");
    EXPECT_EQ(6*7, 42);
}
