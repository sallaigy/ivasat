#include "ivasat/ivasat.h"

#include <gtest/gtest.h>

#include <sstream>

using namespace ivasat;

::testing::AssertionResult assertSat(Instance& instance, Status expectedStatus)
{
  auto actualStatus = instance.check();

  if (actualStatus != expectedStatus) {
    return ::testing::AssertionFailure() << "Expected " << expectedStatus << " but got " << actualStatus << ".";
  }

  if (actualStatus == Status::Sat) {
    // Check if the model is valid
    std::vector<bool> model = instance.model();

    for (size_t i = 0; i < instance.clauses().size(); ++i) {
      const auto& clause = instance.clauses()[i];

      bool result = false;
      for (int varIdx : clause) {
        result |= varIdx < 0 ? !model[-varIdx] : model[varIdx];
      }

      if (!result) {
        return ::testing::AssertionFailure() << "Expected satisfiable instance, but the returned model is not valid for clause #" << i << ".";
      }
    }
  }

  return ::testing::AssertionSuccess();
}

TEST(SolverTest, smoke_test_simple_or)
{
  // (x OR ~x)
  Instance inst(1, {{1, -1}});

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, smoke_test_simple_contradiction)
{
  // (x) AND (~x)
  Instance inst = {1, {{1}, {-1}}};

  EXPECT_TRUE(assertSat(inst, Status::Unsat));
}

TEST(SolverTest, smoke_test_two_variables)
{
  // (x OR y)
  Instance inst = {2, {{1, 2}}};

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, no_variables)
{
  Instance inst(0, {});

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, empty_instance)
{
  Instance inst(4, {});

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, empty_single_clause)
{
  Instance inst(4, {{}});

  EXPECT_TRUE(assertSat(inst, Status::Unsat));
}

TEST(SolverTest, empty_clause)
{
  Instance inst(4, {{}, {1, 2, 3, 4}});

  EXPECT_TRUE(assertSat(inst, Status::Unsat));
}

TEST(SolverTest, negated_first_variable)
{
  // (~x) AND (y)
  Instance inst(2, {{-1}, {2}});

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, negated_second_variable)
{
  Instance inst(3, {
    {1, 2, 3},
    {1, 2, -3},
    {-2}
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, negated_second_variable_2)
{
  // (~y | z) & (x | ~z) & (z)
  Instance inst(3, {{-2, 3}, {1, -3}, {3}});

  EXPECT_TRUE(assertSat(inst, Status::Sat));
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

  EXPECT_TRUE(assertSat(inst, Status::Unsat));
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

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, learning_clauses)
{
  Instance inst(7, {
    {-1, 2},
    {-3, 4},
    {-6, -5, -2},
    {-5, 6},
    {5, 7},
    {-1, 5, -7}
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, failed_literal)
{
  Instance inst(4, {
    {3, 4},
    {-2, -4},
    {-2,-3, 4},
    {1, 2, -4},
    {-1, 2, 4}
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, failed_literal_from_complex_sat)
{
  Instance inst(4, {
    {-3, -2, -1},
    {-2, 3},
    {2, 4},
    {2, -4}
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, unit_clause)
{
  Instance inst(3, {
    {1},
    {2},
    {-1, -2, 3}
  });
}

TEST(SolverTest, unit_clause_unsat)
{
  Instance inst(3, {
    {1},
    {2},
    {-3},
    {-1, -2, 3}
  });
}

TEST(SolverTest, wrong_unsat)
{
  Instance inst(4, {
    {-2, 3},
    {4},
    {1, -3, -4},
    {-1}
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, wrong_unsat_2)
{
  // p cnf 7 7
  //-3 5 0
  //-4 0
  //-2 3 4 0
  //2 -6 0
  //-5 0
  //6 7 0
  //-1 -7 0
  Instance inst(7, {
    {-3, 5},
    {-4},
    {-2, 3, 4},
    {2, -6},
    {-5},
    {6, 7},
    {-1, -7}
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, wrong_unsat_3)
{
  // p cnf 11 11
  //6 8 0
  //-6 8 0
  //3 -8 0
  //-5 9 0
  //5 -7 0
  //-2 5 7 0
  //-3 4 0
  //2 -10 0
  //-4 -9 0
  //9 10 11 0
  //-1 -11 0
  Instance inst(11, {
    {6, 8},
    {-6, 8},
    {3, -8},
    {-5, 9},
    {5, -7},
    {-2, 5, 7},
    {-3, 4},
    {2, -10},
    {-4, -9},
    {9, 10, 11},
    {-1, -11},
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}

TEST(SolverTest, wrong_unsat_4)
{
  // 3 -5 7 0
  //-3 6 0
  //4 0
  //-4 -6 0
  Instance inst(7, {
    {3, -5, 7},
    {-3, 6},
    {4},
    {-4, -6}
  });

  EXPECT_TRUE(assertSat(inst, Status::Sat));
}
