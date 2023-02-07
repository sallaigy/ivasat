#include "ivasat/ivasat.h"

#include <gtest/gtest.h>

using namespace ivasat;

TEST(SolverTest, smoke_test_simple_or)
{
  // (x OR ~x)
  Instance inst(1, {{1, -1}});
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}

TEST(SolverTest, smoke_test_simple_contradiction)
{
  // (x) AND (~x)
  Instance inst = {1, {{1}, {-1}}};
  auto status = inst.check();

  EXPECT_EQ(status, Status::Unsat);
}

TEST(SolverTest, smoke_test_two_variables)
{
  // (x OR y)
  Instance inst = {2, {{1, 2}}};
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}

TEST(SolverTest, no_variables)
{
  Instance inst(0, {});
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}

TEST(SolverTest, empty_instance)
{
  Instance inst(4, {});
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}

TEST(SolverTest, negated_first_variable)
{
  // (~x) AND (y)
  Instance inst(2, {{-1}, {2}});
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}

TEST(SolverTest, negated_second_variable)
{
  // (~x) AND (y)
  Instance inst(3, {{1, 2, 3}, {1, 2, -3}, {-2}});
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}

TEST(SolverTest, negated_second_variable_2)
{
  // (~y | z) & (x | ~z) & (z)
  Instance inst(3, {{-2, 3}, {1, -3}, {3}});
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}

TEST(SolverTest, complex_unsat)
{
  // (a | ~b) & (~a | c | ~d) & (a | c | ~d) & (~c | ~e) & (~c | e) & (c | d)
  Instance inst(5, {
    {1, -2},
    {-1, 3, -4},
    {1, 3, -4},
    {-3, -5},
    {-3, 5},
    {3, 4}
  });
  auto status = inst.check();

  EXPECT_EQ(status, Status::Unsat);
}

TEST(SolverTest, complex_sat)
{
  // (a | ~b) & (a | c | ~d) & (~c | ~e) & (~c | e) & (c | d)
  Instance inst(5, {
    {1, -2},
    {1, 3, -4},
    {-3, -5},
    {-3, 5},
    {3, 4}
  });
  auto status = inst.check();

  EXPECT_EQ(status, Status::Sat);
}
