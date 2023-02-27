#include "ivasat/ivasat.h"

#include <ranges>
#include <set>
#include <algorithm>
#include <iostream>
#include <optional>
#include <cassert>
#include <map>
#include <sstream>

using namespace ivasat;

namespace ivasat
{

struct Statistics
{
  unsigned checkedStates = 0;
  unsigned checkedFullCombinations = 0;
};

enum class Tribool
{
  False,
  True,
  Unknown
};

Tribool operator&(Tribool left, Tribool right)
{
  if (left == Tribool::False || right == Tribool::False) {
    return Tribool::False;
  }

  if (left == Tribool::Unknown || right == Tribool::Unknown) {
    return Tribool::Unknown;
  }

  return Tribool::True;
}

Tribool operator|(Tribool left, Tribool right)
{
  if (left == Tribool::True || right == Tribool::True) {
    return Tribool::True;
  }

  if (left == Tribool::Unknown || right == Tribool::Unknown) {
    return Tribool::Unknown;
  }

  return Tribool::False;
}

Tribool operator~(Tribool value)
{
  if (value == Tribool::True) {
    return Tribool::False;
  }

  if (value == Tribool::False) {
    return Tribool::True;
  }

  return Tribool::Unknown;
}

static Tribool liftBool(bool value)
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

  static constexpr int UnknownIndex = -1;

public:
  explicit Solver(const Instance& instance)
    : mClauses(instance.clauses()), mVariableState(instance.numVariables() + 1, Tribool::Unknown),
    mImplications(instance.numVariables() + 1, UnknownIndex), mAssignedAtLevel(instance.numVariables() + 1, UnknownIndex)
  {}

  Status check();

  std::vector<bool> model() const;

  const Statistics& statistics() const
  {
    return mStats;
  }

  void assignUnitClause(int variableIndex, bool value, int clauseIndex)
  {
    this->assignVariable(variableIndex, value);

    assert(mImplications[variableIndex] == UnknownIndex && "No implications should exists for a freshly assigned unit clause");
    mImplications[variableIndex] = clauseIndex;
  }

  void assignVariable(int variableIndex, bool booleanValue)
  {
    Tribool value = liftBool(booleanValue);
    assert(mVariableState[variableIndex] == value || mVariableState[variableIndex] == Tribool::Unknown);

    if (mVariableState[variableIndex] == value) {
      // This variable value has already been set by a previous propagation, there is nothing to do.
      return;
    }

    mVariableState[variableIndex] = value;

    assert(mAssignedAtLevel[variableIndex] == UnknownIndex && "No assignment level should exist for an unassigned variable");
    mAssignedAtLevel[variableIndex] = this->decisionLevel();
    mTrail.emplace_back(variableIndex, booleanValue);
  }

  void undoAssignment(size_t variableIndex)
  {
    assert(mVariableState[variableIndex] != Tribool::Unknown && "Cannot undo an assignment that did not take place");

    mVariableState[variableIndex] = Tribool::Unknown;
    mAssignedAtLevel[variableIndex] = UnknownIndex;
    mImplications[variableIndex] = UnknownIndex;
  }

  bool propagateUnitClause(int variableIndex, bool value, size_t clauseIndex);

  void pushDecision(int varIdx, bool value)
  {
    mTrailIndices.emplace_back(mTrail.size());
    mDecisions.emplace_back(varIdx, value);
    this->assignVariable(varIdx, value);
  }

  void popDecision()
  {
    size_t lastIdx = mTrailIndices.back();
    mTrailIndices.pop_back();

    for (size_t i = lastIdx; i < mTrail.size(); ++i) {
      int varIdx = mTrail[i].first;
      this->undoAssignment(varIdx);
    }
    mDecisions.pop_back();

    if (!mTrail.empty()) {
      mTrail.erase(mTrail.begin() + lastIdx, mTrail.end());
    }
  }

  int unassignedLiteralIndex(size_t clauseIdx)
  {
    for (int literal : mClauses[clauseIdx]) {
      int finalIdx = literal < 0 ? -literal : literal;
      auto currentValue = mVariableState[finalIdx];
      if (currentValue == Tribool::Unknown) {
        return literal;
      }
    }

    assert(false && "Should be unreachable!");
    return 0;
  }

private:
  bool isValid();

  bool isValidChoice(int index, bool value)
  {
    return std::ranges::none_of(mTrail, [&](const std::pair<int, bool>& pair) {
      return pair.first == index && pair.second != value;
    });
  }

  void preprocess();

  ClauseStatus checkClause(const std::vector<int>& clause);

  void analyzeConflict(size_t domSetIndex);

  std::vector<std::pair<int, bool>> reasonFor(std::pair<int, bool> literal);

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

  int firstUnassignedIndex(int start) const
  {
    for (int i = start; i < mVariableState.size(); ++i) {
      if (mVariableState[i] == Tribool::Unknown) {
        return i;
      }
    }

    // This really should not happen in a valid solver state
    assert(false && "There must be an unassigned index in a valid solver state!");
    return UnknownIndex;
  }

  // Debug methods
  //==----------------------------------------------------------------------==//

  /// Write the current implication graph to standard output in DOT format. If the conflicting clause index is not
  /// `UnknownIndex`, a conflict node will be present in the graph as well.
  void dumpImplicationGraph(int conflictClauseIndex = UnknownIndex);

  // Fields
  //==----------------------------------------------------------------------==//

  // Clause database
  std::vector<std::vector<int>> mClauses;

  // Internal solver state
  std::vector<Tribool> mVariableState;
  std::vector<std::pair<int, bool>> mDecisions;

  // For each assigned variable index, the index of the variable and clause that implied its value.
  // The value for decided and unassigned variables is going to be -1.
  std::vector<int> mImplications;

  // For each assigned variable index, the decision level at which it was assigned to a value.
  // For unassigned variables, the value is going to be -1.
  std::vector<int> mAssignedAtLevel;

  // List of assignments in chronological order.
  std::vector<std::pair<int, bool>> mTrail;
  std::vector<size_t> mTrailIndices;

  Statistics mStats;
};

} // namespace

std::ostream& ivasat::operator<<(std::ostream& os, Status status)
{
  switch (status) {
    case Status::Sat:
      os << "Sat";
      break;
    case Status::Unsat:
      os << "Unsat";
      break;
    case Status::Unknown:
      os << "Unknown";
      break;
  }

  return os;
}

Status Instance::check()
{
  Solver solver{*this};
  auto status = solver.check();

  std::cout << "Total checked states: " << solver.statistics().checkedStates << "\n";
  std::cout << "Total checked full combinations: " << solver.statistics().checkedFullCombinations << "\n";

  if (status == Status::Sat) {
    mModel = solver.model();
  }

  return status;
}

Solver::ClauseStatus Solver::checkClause(const std::vector<int>& clause)
{
  ClauseStatus status = ClauseStatus::Conflicting;

  for (int varIdx : clause) {
    bool shouldNegate;
    int finalIndex;

    if (varIdx < 0) {
      shouldNegate = true;
      finalIndex = -varIdx;
    } else {
      shouldNegate = false;
      finalIndex = varIdx;
    }

    Tribool variableValue = Tribool::Unknown;
    if (mVariableState[finalIndex] == Tribool::Unknown) {
      if (status == ClauseStatus::Unit || status == ClauseStatus::Unresolved) {
        status = ClauseStatus::Unresolved;
        continue;
      } else {
        status = ClauseStatus::Unit;
        continue;
      }
    } else {
      variableValue = mVariableState[finalIndex];
      variableValue = shouldNegate ? ~variableValue : variableValue;
    }

    if (variableValue == Tribool::True) {
      return ClauseStatus::Satisfied;
    }
  }

  return status;
}

bool Solver::isValid()
{
  mStats.checkedStates++;
  if (mDecisions.size() == mVariableState.size() - 1) {
    mStats.checkedFullCombinations++;
  }

  for (size_t i = 0; i < mClauses.size(); ++i) {
    auto clauseStatus = checkClause(mClauses[i]);
    if (clauseStatus == ClauseStatus::Conflicting) {
      this->analyzeConflict(i);
      return false;
    }

    if (clauseStatus == ClauseStatus::Unit) {
      // The clause is not satisfied but the last literal is unassigned, so we can propagate its value
      int lastIndex = unassignedLiteralIndex(i);
      bool shouldNegate = lastIndex < 0;
      int variableIndex = shouldNegate ? -lastIndex : lastIndex;

      bool sucessfulPropagation = this->propagateUnitClause(variableIndex, !shouldNegate, i);
      if (!sucessfulPropagation) {
        return false;
      }
    }
  }

  return true;
}

void Solver::preprocess()
{
  // Order variables inside clauses by index
  for (auto& clause : mClauses) {
    std::ranges::sort(clause, [](int l, int r) {
      return std::abs(l) < std::abs(r);
    });
  }

  // Order clauses by size
  std::ranges::sort(mClauses, [](auto& l, auto& r) {
    if (l.size() < r.size()) {
      return true;
    }

    return std::ranges::lexicographical_compare(l, r, [](int leftVal, int rightVal) {
      return std::abs(leftVal) < std::abs(rightVal);
    });
  });
}

Status Solver::check()
{
  if (mClauses.empty()) {
    std::ranges::for_each(mVariableState, [](auto& v) { v = Tribool::True; });
    return Status::Sat;
  }

  this->preprocess();

  // Start search
  std::pair<int, bool> nextState = {1, true};

  while (true) {
    auto [currentIndex, currentValue] = nextState;

    // Check if the current state is okay
    bool shouldBacktrack = false;

    this->pushDecision(currentIndex, currentValue);

    if (isValid()) {
      // Is this a complete state?
      if (numAssigned() == mVariableState.size() - 1) {
        return Status::Sat;
      }

      int newState = firstUnassignedIndex(currentIndex);
      if (isValidChoice(newState, true)) {
        nextState = {newState, true};
      } else {
        nextState = {newState, false};
      }
    } else if (currentValue == true) {
      this->popDecision();
      // Try again with setting the current index to false
      nextState = {currentIndex, false};
    } else {
      shouldBacktrack = true;
    }

    assert((nextState != std::make_pair(currentIndex, currentValue)) || shouldBacktrack);

    if (shouldBacktrack) {
      // We will have to backtrack to the closest non-false state
      bool hasNextState = false;
      for (auto it = mDecisions.rbegin(); it != mDecisions.rend(); ++it) {
        auto [decidedVariable, decidedValue] = *it;
        Tribool previousVariableState = mVariableState[decidedVariable];
        this->popDecision();

        if (previousVariableState == Tribool::True && isValidChoice(decidedVariable, false)) {
          nextState = {decidedVariable, false};
          hasNextState = true;
          break;
        }
      }

      if (!hasNextState) {
        return Status::Unsat;
      }
    }
  }
}

bool Solver::propagateUnitClause(int variableIndex, bool value, size_t clauseIndex)
{
  this->assignUnitClause(variableIndex, value, clauseIndex);

  bool changed = true;
  while (changed) {
    changed = false;
    for (size_t i = 0; i < mClauses.size(); ++i) {
      const auto& clause = mClauses[i];
      auto clauseStatus = checkClause(clause);
      if (clauseStatus == ClauseStatus::Conflicting) {
        this->analyzeConflict(i);
        return false;
      }

      if (clauseStatus == ClauseStatus::Unit) {
        // The clause is not satisfied but there is one unassigned literal, so we can propagate its value
        int lastIndex = unassignedLiteralIndex(i);
        bool shouldNegate = lastIndex < 0;
        int finalIndex = shouldNegate ? -lastIndex : lastIndex;

        this->assignUnitClause(finalIndex, !shouldNegate, i);
        changed = true;
      }
    }
  }

  return true;
}

void Solver::analyzeConflict(size_t conflictClauseIndex)
{
  // Find a cut of the implication graph through a unique implication point (UIP).
  // The UIP is a node at decision level `d` such that every path from the decision variable at level `d` to the
  // conflict node must go through it.

  // A cut for a UIP `l` is a pair (A,B) where
  //  - B contains all successors of `l` where there is a path to the conflict node
  //  - A contains all the rest of nodes

  // TODO: Debug
  this->dumpImplicationGraph(conflictClauseIndex);

  // TODO: There is a more sophisticated linear-time algorithm described in the Minisat paper

  // Given the last decision literal as a flow graph source (decision literals are always zero in-degree), the first
  // UIP will be the closest dominator of the conflict node.
  //  D(n_0) = { n_0 }
  //  D(n) = { n } U intersect(for p in pred(n): D(p))
  std::vector<bool> seen(mTrail.size() + 1, false);

  // The dominator set of each node on the trail
  std::map<int, int> trailIndices;
  for (int i = 0; i < mTrail.size(); ++i) {
    trailIndices[mTrail[i].first] = i;
  }

  std::vector<std::vector<bool>> dominators(mTrail.size() + 1, std::vector<bool>(mTrail.size() + 1, false));

  size_t conflictNodeIdx = mTrail.size();

  auto preds = [this, &trailIndices](size_t domSetIndex) {
    std::vector<int> result;

    if (domSetIndex == mTrail.size()) {

    } else {
      int literalIndex = mTrail[domSetIndex].first;
      int impliedByClause = mImplications[literalIndex];
      if (impliedByClause == UnknownIndex) {
        return result;
      }

      for (int clauseLit: mClauses[impliedByClause]) {
        int varIdx = clauseLit < 0 ? -clauseLit : clauseLit;

        if (varIdx != literalIndex) {
          result.push_back(varIdx);
        }
      }
    }

    return result;
  };

  int lastDecisionIdx = trailIndices[mDecisions.back().first];
  dominators[lastDecisionIdx][lastDecisionIdx] = true;

  // Iterative algorithm for finding dominators
  for (int i = 0; i < dominators.size(); ++i) {
    if (i != lastDecisionIdx) {
      // Initial condition: set all vertices (except the source) to be dominated by every other vertex
      for (int j = 0; j < dominators.size(); ++j) {
        dominators[i][j] = true;
      }
    }
  }

  bool changed = true;
  while (changed) {
    changed = false;
    for (int i = 0; i < dominators.size(); ++i) {
      if (i == lastDecisionIdx) {
        continue;
      }

      auto prev = dominators[i];
      std::vector<bool> predDoms(dominators[i].size(), true);
      for (int p : preds(i)) {
        int predDomIdx = trailIndices[p];
        for (size_t j = 0; j < dominators.size(); ++j) {
          std::cout << "(" << i << ", " << j << ", " << predDomIdx << ")" << std::endl;
          predDoms[j] = predDoms[j] && dominators[predDomIdx][j];

        }
      }

      dominators[i] = predDoms;
      dominators[i][i] = true;

      if (prev != dominators[i]) {
        changed = true;
      }
    }
  }

  std::cout << dominators.size() << "\n";


}

void Solver::dumpImplicationGraph(int conflictClauseIndex)
{
  const auto& conflictClause = mClauses[conflictClauseIndex];
  std::stringstream ss;

  ss << "digraph G {\n";

  for (const auto& [varIdx, value] : mTrail) {
    int assignedAt = mAssignedAtLevel[varIdx];
    ss << "node_" << varIdx << " [label=\"" << varIdx << ":" << std::boolalpha << value << "@" << assignedAt << "\"];\n";
  }

  for (int i = 0; i < mImplications.size(); ++i) {
    int clauseIdx = mImplications[i];

    if (clauseIdx == UnknownIndex) {
      continue;
    }

    for (int lit : mClauses[clauseIdx]) {
      int varIdx = lit < 0 ? -lit : lit;
      if (varIdx != i) {
        ss << "node_" << varIdx << " -> " << "node_" << i << "[label=\"  " << clauseIdx << "\"];\n";
      }
    }
  }

  for (int lit : conflictClause) {
    int finalIdx = lit < 0 ? -lit : lit;

    ss << "node_" << finalIdx << " -> " << "conflict[label=\"" << conflictClauseIndex << "\"];\n";
  }

  ss << "}";

  std::cout << ss.str() << std::endl;
}

std::vector<bool> Solver::model() const
{
  std::vector<bool> result;
  result.push_back(false);
  for (size_t i = 1; i < mVariableState.size(); ++i) {
    assert(mVariableState[i] != Tribool::Unknown);
    result.push_back(mVariableState[i] == Tribool::True);
  }

  return result;
}

std::vector<bool> Instance::model() const
{
  return mModel;
}
