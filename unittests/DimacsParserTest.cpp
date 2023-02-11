#include "ivasat/ivasat.h"

#include <sstream>

#include <gtest/gtest.h>

using namespace ivasat;

TEST(DimacsParserTest, simple_clause)
{
  std::istringstream stream{R"(
p cnf 1 2
1 0
-1 0
)"};
  auto instance = parseDimacs(stream);

  ASSERT_NE(instance, nullptr);

  EXPECT_EQ(instance->numVariables(), 1);

  std::vector<std::vector<int>> expectedClauses = {
    {1},
    {-1}
  };
  EXPECT_EQ(instance->clauses(), expectedClauses);
}

TEST(DimacsParserTest, simple_clause_with_comments_in_header)
{
  std::istringstream stream{R"(
c This is a simple clause
p cnf 1 2
1 0
-1 0
)"};
  auto instance = parseDimacs(stream);

  ASSERT_NE(instance, nullptr);

  EXPECT_EQ(instance->numVariables(), 1);

  std::vector<std::vector<int>> expectedClauses = {
    {1},
    {-1}
  };
  EXPECT_EQ(instance->clauses(), expectedClauses);
}
