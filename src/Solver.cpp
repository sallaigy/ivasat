#include "ivasat/ivasat.h"

#include <ranges>
#include <set>
#include <algorithm>
#include <iostream>
#include <optional>
#include <cassert>

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
    mPropagations.emplace_back(variableIndex, value);
    this->assignVariable(variableIndex, value);

    assert(mImplications[variableIndex] == UnknownIndex && "No implications should exists for a freshly assigned unit clause");
    mImplications[variableIndex] = clauseIndex;
  }

  void assignVariable(int variableIndex, bool booleanValue)
  {
    Tribool value = booleanValue ? Tribool::True : Tribool::False;
    assert(mVariableState[variableIndex] == value || mVariableState[variableIndex] == Tribool::Unknown);

    if (mVariableState[variableIndex] == value) {
      // This variable value has already been set by a previous propagation, there is nothing to do.
      return;
    }

    mVariableState[variableIndex] = value;
    ++mNumAssignedVariables;

    assert(mAssignedAtLevel[variableIndex] == UnknownIndex && "No assignment level should exist for an unassigned variable");
    mAssignedAtLevel[variableIndex] = this->decisionLevel();
  }

  void undoAssignment(size_t variableIndex)
  {
    if (mVariableState[variableIndex] == Tribool::Unknown) {
      // TODO: Should this be possible?
      return;
    }

    mVariableState[variableIndex] = Tribool::Unknown;
    mAssignedAtLevel[variableIndex] = UnknownIndex;
    mImplications[variableIndex] = UnknownIndex;
    --mNumAssignedVariables;
  }

  bool propagateUnitClause(int variableIndex, bool value, size_t clauseIndex);

  void pushState()
  {
    mPropagationIndices.emplace_back(mPropagations.size());
  }

  void popState()
  {
    size_t lastIdx = mPropagationIndices.back();
    mPropagationIndices.pop_back();

    for (size_t i = lastIdx; i < mPropagations.size(); ++i) {
      int varIdx = mPropagations[i].first;
      this->undoAssignment(varIdx);
    }

    if (!mPropagations.empty()) {
      mPropagations.erase(mPropagations.begin() + lastIdx, mPropagations.end());
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
    return std::ranges::none_of(mPropagations, [&](const std::pair<int, bool>& pair) {
      return pair.first == index && pair.second != value;
    });
  }

  void preprocess();

  ClauseStatus checkClause(size_t clauseIdx);

  // Some helper methods
  //==----------------------------------------------------------------------==//
  size_t decisionLevel() const
  {
    return mDecisions.size();
  }

  size_t numAssigned() const
  {
    //return std::ranges::count_if(mVariableState, [](auto& v) { return v != Tribool::Unknown; });
    assert(std::ranges::count_if(mVariableState, [](auto& v) { return v != Tribool::Unknown; }) == mNumAssignedVariables);
    return mNumAssignedVariables;
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


  // Fields
  //==----------------------------------------------------------------------==//

  // Clause database
  std::vector<std::vector<int>> mClauses;

  // Internal solver state
  std::vector<Tribool> mVariableState;
  std::vector<std::pair<int, bool>> mDecisions;
  std::vector<size_t> mPropagationIndices;
  std::vector<std::pair<int, bool>> mPropagations;

  // For each assigned variable index, the index of the clause that implied its value.
  // The value for decided and unassigned variables is going to be -1.
  std::vector<int> mImplications;

  // For each assigned variable index, the decision level at which it was assigned to a value.
  // For unassigned variables, the value is going to be -1.
  std::vector<int> mAssignedAtLevel;

  unsigned mNumAssignedVariables = 0;

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

Solver::ClauseStatus Solver::checkClause(size_t clauseIdx)
{
  const std::vector<int>& clause = mClauses[clauseIdx];

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
    auto clauseStatus = checkClause(i);
    if (clauseStatus == ClauseStatus::Conflicting) {
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

    mDecisions.emplace_back(currentIndex, currentValue);
    this->assignVariable(currentIndex, currentValue);

    this->pushState();
    if (isValid()) {
      // Is this a complete state?
      if (numAssigned() == mVariableState.size() - 1) {
        return Status::Sat;
      }

      int newState = firstUnassignedIndex(currentIndex);
      //int newState = currentIndex + 1;
      if (isValidChoice(newState, true)) {
        nextState = {newState, true};
      } else {
        nextState = {newState, false};
      }
    } else if (currentValue == true) {
      this->undoAssignment(currentIndex);
      this->popState();
      mDecisions.pop_back();
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
        this->undoAssignment(decidedVariable);
        this->popState();
        mDecisions.pop_back();

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
      auto clauseStatus = checkClause(i);
      if (clauseStatus == ClauseStatus::Conflicting) {
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
