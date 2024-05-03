#ifndef IVA_SAT_SOLVER_H
#define IVA_SAT_SOLVER_H

#include "ivasat/ivasat.h"

#include <vector>
#include <algorithm>
#include <cassert>
#include <queue>
#include <set>
#include <limits>

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

  constexpr Literal(int index, bool value)
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
  explicit Clause(std::vector<Literal> literals, bool isLearned = false)
    : mLiterals(std::move(literals)), mIsLearned(isLearned)
  {
  }

  Clause(const Clause&) = default;
  Clause& operator=(const Clause&) = default;

  Literal& operator[](int index)
  {
    return mLiterals[index];
  }

  const Literal& operator[](int index) const
  {
    return mLiterals[index];
  }

  Literal back() const
  {
    return mLiterals.back();
  }

  bool isLearned() const
  {
    return mIsLearned;
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

  // Manipulation
  void remove(Literal lit)
  {
    mLiterals.erase(std::remove(mLiterals.begin(), mLiterals.end(), lit), mLiterals.end());
  }

  template<class Predicate>
  long remove(Predicate&& pred)
  {
    auto pos = std::remove_if(mLiterals.begin(), mLiterals.end(), pred);
    long numRemoved = std::distance(pos, mLiterals.end());
    mLiterals.erase(pos, mLiterals.end());

    return numRemoved;
  }

  double activity() const
  {
    return mActivity;
  }

  void bumpActivity()
  {
    mActivity += 1;
  }

  void decayActivity(double factor)
  {
    mActivity *= factor;
  }

  bool isLocked() const
  {
    return mIsLocked;
  }

  void lock()
  {
    mIsLocked = true;
  }

  void unlock()
  {
    mIsLocked = false;
  }

  void markAsGarbage()
  {
    mIsGarbage = true;
  }

  bool isGarbage() const
  {
    return mIsGarbage;
  }

private:
  std::vector<Literal> mLiterals;
  bool mIsLearned;
  bool mIsGarbage = false;
  bool mIsLocked = false;
  double mActivity = 1.0;
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
    unsigned variables = 0;
    unsigned clauses = 0;
    unsigned decisions = 0;
    unsigned checkedFullCombinations = 0;
    unsigned propagations = 0;
    unsigned learnedClauses = 0;
    unsigned clausesEliminatedBySimplification = 0;
    unsigned restarts = 0;
    unsigned conflicts = 0;
    unsigned pureLiterals = 0;
    unsigned int clausesEliminatedByReduce = 0;
  };

  struct Watch
  {
    int clauseIdx;
    Literal lit;
  };

  static constexpr int UnknownIndex = -1;

  static constexpr double DefaultActivityDecay = 0.9;

public:
  explicit Solver(const Instance& instance);

  Status check();

  std::vector<bool> model() const;

  void dumpStats(std::ostream& os) const;

  // Solver implementation
  //==---------------------------------------------------------------------==//
private:
  /// Simplify the clause database, removing false literals and true clauses.
  void simplify();

  /// Reduce the clause database, remove old learned clauses
  void reduce();

  bool preprocess();

  void resetWatches();

  // Assignments and decisions
  //==---------------------------------------------------------------------==//

  void assignUnitClause(Literal literal, int clauseIndex);

  void assignVariable(Literal literal);

  void undoAssignment(size_t variableIndex);

  void pushDecision(Literal literal);

  void popDecision();

  /// Pop decisions until `level`.
  void popDecisionUntil(int level);

  void watchClause(int clause);

  Tribool value(Literal literal);

  // Unit propagation
  //==---------------------------------------------------------------------==//

  int propagate();

  void enqueue(Literal literal);

  // Heuristics
  //==---------------------------------------------------------------------==//

  void decayVariableActivities();
  void bumpVariableActivity(std::vector<Literal>& newClause);

  void decayClauseActivities();

  // Clause learning
  //==---------------------------------------------------------------------==//

  int analyzeConflict(int conflictClauseIndex, std::vector<Literal>& newClause);

  [[nodiscard]] std::vector<Literal> lastUniqueImplicationPointCut(int conflictClauseIndex);
  [[nodiscard]] int firstUniqueImplicationPointCut(int conflictClauseIndex, std::vector<Literal>& newClause);

  /// Calculates the predecessors of \p lit in the implication graph.
  void fillImplyingPredecessors(Literal lit, std::vector<Literal>& result);

  // Some helper methods
  //==----------------------------------------------------------------------==//

  int decisionLevel() const
  {
    return static_cast<int>(mDecisions.size());
  }

  size_t numAssigned() const
  {
    assert(std::ranges::count_if(mVariableState, [](auto& v) { return v != Tribool::Unknown; }) == mTrail.size());
    return mTrail.size();
  }

  int pickDecisionVariable() const;

  // Debug methods
  //==----------------------------------------------------------------------==//

  /// Write the current implication graph to standard output in DOT format. If the conflicting clause index is not
  /// `UnknownIndex`, a conflict node will be present in the graph as well.
  void dumpImplicationGraph(int conflictClauseIndex = UnknownIndex);

  // Fields
  //==----------------------------------------------------------------------==//

  // Clause database
  std::vector<Clause> mClauses;
  std::vector<std::vector<Watch>> mWatches;

  // Internal solver state
  std::vector<Tribool> mVariableState;
  std::vector<Literal> mDecisions;
  std::vector<double> mActivity;
  std::deque<int> mQueue;

  // For each assigned variable index, the index of the clause that implied its value.
  // The value for decided and unassigned variables is going to be -1.
  std::vector<int> mImplications;

  // For each assigned variable index, the decision level at which it was assigned to a value.
  // For unassigned variables, the value is going to be -1.
  std::vector<int> mAssignedAtLevel;

  // List of assignments in chronological order.
  std::vector<Literal> mTrail;
  std::vector<int> mTrailIndices;

  // Heuristics
  unsigned mRestartsSinceLastSimplify = std::numeric_limits<unsigned>::max();
  unsigned mNumLearnedClauses = 0;

  Statistics mStats;
};


} // namespace ivasat

#endif //IVA_SAT_SOLVER_H
