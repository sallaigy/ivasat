#ifndef IVA_SAT_SOLVER_H
#define IVA_SAT_SOLVER_H

#include "ivasat/ivasat.h"

#include <vector>
#include <algorithm>
#include <cassert>
#include <queue>

namespace ivasat
{

/// Represents a literal inside of a SAT problem, that is a pair of (variable, value).
class Literal
{
public:
  explicit Literal(int data)
    : mData(data)
  {
    assert(data != 0 && "Literal data must be strictly positive or negative!");
  }

  Literal(int index, bool value)
    : mData(value ? index : -index)
  {
    assert(index > 0 && "A literal cannot have a zero or negative index!");
  }

  Literal(const Literal&) = default;
  Literal& operator=(const Literal&) = default;

  auto operator<=>(const Literal& other) const = default;

  [[nodiscard]] int index() const
  {
    return isNegated() ? -mData : mData;
  }

  [[nodiscard]] bool value() const
  {
    return !isNegated();
  }

  [[nodiscard]] bool isNegated() const
  {
    return mData < 0;
  }

  [[nodiscard]] Literal negate() const
  {
    return Literal(-mData);
  }

private:
  int mData;
};

class Clause
{
public:
  explicit Clause(std::vector<Literal> literals)
    : mLiterals(std::move(literals))
  {
    std::ranges::sort(mLiterals);
  }

  Clause(const Clause&) = default;
  Clause& operator=(const Clause&) = default;

  const Literal& operator[](int index) const
  {
    return mLiterals[index];
  }

  // Iterator support
  using const_iterator = std::vector<Literal>::const_iterator;
  const_iterator begin() const
  {
    return mLiterals.begin();
  }
  const_iterator end() const
  {
    return mLiterals.end();
  }
  size_t size() const
  {
    return mLiterals.size();
  }

private:
  std::vector<Literal> mLiterals;
};

enum class Tribool
{
  False,
  True,
  Unknown
};

Tribool operator~(Tribool value);

inline Tribool liftBool(bool value)
{
  return value ? Tribool::True : Tribool::False;
}

class Solver
{
  enum class ClauseStatus
  {
    Satisfied,
    Conflicting,
    Unit,
    Unresolved
  };

  struct Statistics
  {
    unsigned checkedStates = 0;
    unsigned checkedFullCombinations = 0;
    unsigned learnedClauses = 0;
  };

  static constexpr int UnknownIndex = -1;

public:
  explicit Solver(const Instance& instance);

  Status check();

  std::vector<bool> model() const;

  const Statistics& statistics() const
  {
    return mStats;
  }

  void assignUnitClause(Literal literal, int clauseIndex);

  void assignVariable(Literal literal);

  void undoAssignment(size_t variableIndex);

  bool propagate();

  void pushDecision(Literal literal);

  void popDecision();

  /// Pop the decision level which assigned `varIdx` and all decisions following it.
  void popDecisionUntil(int varIdx);

  Literal unassignedLiteral(const Clause& clause)
  {
    for (Literal literal : clause) {
      auto currentValue = mVariableState[literal.index()];
      if (currentValue == Tribool::Unknown) {
        return literal;
      }
    }

    assert(false && "Should be unreachable!");
    return Literal{0};
  }

private:
  bool isValidChoice(int index, bool value)
  {
    return std::ranges::none_of(mTrail, [&](Literal lit) {
      return lit.index() == index && lit.value() != value;
    });
  }

  void preprocess();

  ClauseStatus checkClause(const Clause& clause);

  void analyzeConflict(size_t trailIndex);

  // Some helper methods
  //==----------------------------------------------------------------------==//
  size_t decisionLevel() const
  {
    return mDecisions.size();
  }

  size_t numAssigned() const
  {
    assert(std::ranges::count_if(mVariableState, [](auto& v) { return v != Tribool::Unknown; }) == mTrail.size());
    return mTrail.size();
  }

  int pickDecisionVariable(int start) const;

  // Debug methods
  //==----------------------------------------------------------------------==//

  /// Write the current implication graph to standard output in DOT format. If the conflicting clause index is not
  /// `UnknownIndex`, a conflict node will be present in the graph as well.
  void dumpImplicationGraph(int conflictClauseIndex = UnknownIndex);

  // Fields
  //==----------------------------------------------------------------------==//

  // Clause database
  std::vector<Clause> mClauses;

  // Internal solver state
  std::vector<Tribool> mVariableState;
  std::vector<Literal> mDecisions;

  // For each assigned variable index, the index of the variable and clause that implied its value.
  // The value for decided and unassigned variables is going to be -1.
  std::vector<int> mImplications;

  // For each assigned variable index, the decision level at which it was assigned to a value.
  // For unassigned variables, the value is going to be -1.
  std::vector<int> mAssignedAtLevel;

  // List of assignments in chronological order.
  std::vector<Literal> mTrail;
  std::vector<size_t> mTrailIndices;

  Statistics mStats;
};


} // namespace ivasat

#endif //IVA_SAT_SOLVER_H
