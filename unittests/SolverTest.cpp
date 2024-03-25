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


TEST(SolverTest, wrong_unsat_5)
{
  std::stringstream ss(R"(
p cnf 9 9
2 3 6 0
-3 5 6 0
-3 -5 6 0
-6 9 0
-6 -9 0
-2 4 0
-4 -7 0
7 8 0
-1 -8 0
)");
  auto inst = parseDimacs(ss);

  EXPECT_TRUE(assertSat(*inst, Status::Sat));
}

TEST(SolverTest, simplify_top_level_with_learned_clause)
{
  std::stringstream ss(R"(
p cnf 7 7
-2 0
4 6 0
-4 7 0
-4 -7 0
3 -6 0
-1 5 0
-3 -6 0
  )");
  auto inst = parseDimacs(ss);

  EXPECT_TRUE(assertSat(*inst, Status::Unsat));
}

TEST(SolverTest, learning_contradictory_unit_clause)
{
  std::stringstream ss(R"(
p cnf 10 9
4 5 0
4 -5 0
-4 9 0
7 8 0
-3 0
1 2 0
6 8 0
-8 -9 0
-6 -7 0
  )");
  auto inst = parseDimacs(ss);

  EXPECT_TRUE(assertSat(*inst, Status::Unsat));
}


TEST(SolverTest, learning_unit_clause_backjump_to_top)
{
  std::stringstream ss(R"(
p cnf 12 11
-2 4 0
5 7 0
5 -7 0
-5 11 0
9 10 0
1 3 0
6 8 0
-3 -6 0
-1 8 10 0
-10 -11 0
-8 -9 0
)");
  auto inst = parseDimacs(ss);

  EXPECT_TRUE(assertSat(*inst, Status::Unsat));
}

TEST(SolverTest, two_watched_literals_list_index_error_regression)
{
  std::stringstream ss(R"(
p cnf 9 9
-1 -4 0
-1 -3 0
4 9 0
-2 3 5 0
-5 -9 0
2 6 0
-8 -9 0
7 8 0
-6 -7 0
)");
  auto inst = parseDimacs(ss);

  EXPECT_TRUE(assertSat(*inst, Status::Sat));
}

TEST(SolverTest, two_watched_literals_wrong_unsat_regression)
{
  std::stringstream ss(R"(
p cnf 6 6
-3 4 0
-2 -3 -4 0
-2 3 -5 0
5 -6 0
-1 5 6 0
1 6 0
)");
  auto inst = parseDimacs(ss);

  EXPECT_TRUE(assertSat(*inst, Status::Sat));
}

TEST(SolverTest, two_watched_literals_wrong_unsat_regression2)
{
  std::stringstream ss(R"(
p cnf 15 15
2 3 0
-2 3 0
-3 7 0
-7 10 0
-10 -15 0
-12 15 0
-5 15 0
4 5 12 0
-4 -6 0
6 13 0
-9 -13 0
9 14 0
-8 -14 0
8 -11 0
-1 11 0
)");
  auto inst = parseDimacs(ss);

  EXPECT_TRUE(assertSat(*inst, Status::Sat));
}