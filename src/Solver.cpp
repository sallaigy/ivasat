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

class Solver
{
  enum class ClauseStatus
  {
    Satisfied,
    Conflicting,
    Unit,
    Unresolved
  };

public:
  explicit Solver(const Instance& instance)
    : mVariableState(instance.numVariables() + 1, Tribool::Unknown), mClauses(instance.clauses())
  {}

  Status check();

  std::vector<bool> model() const;

  const Statistics& statistics() const
  {
    return mStats;
  }

  void assignUnitClause(int variableIndex, bool value)
  {
    mPropagations.emplace_back(variableIndex, value);
    this->assignVariable(variableIndex, value);
  }

  void assignVariable(int variableIndex, bool booleanValue)
  {
    Tribool value = booleanValue ? Tribool::True : Tribool::False;

    if (mVariableState[variableIndex] == value) {
      // This variable value has already been set by a previous propagation, there is nothing to do.
      return;
    }

    if (variableIndex == mFirstUnknownIndex) {
      for (size_t i = mFirstUnknownIndex + 1; i < mVariableState.size(); ++i) {
        if (mVariableState[i] == Tribool::Unknown) {
          mFirstUnknownIndex = i;
          break;
        }
      }
    }
    mNumAssignedVariables++;
    mVariableState[variableIndex] = value;
  }

  bool propagateUnitClause(int variableIndex, bool value)
  {
    this->assignUnitClause(variableIndex, value);

    bool changed = true;
    while (changed) {
      changed = false;
      for (size_t i = 0; i < mClauses.size(); ++i) {
        auto clauseStatus = checkClause(i);
        if (clauseStatus == ClauseStatus::Conflicting) {
          // The propagation set forward by the last decision led to a conflict, so we can learn that the last set
          // literal cannot have its current value in any interpretation
          return false;
        }

        if (clauseStatus == ClauseStatus::Unit) {
          // The clause is not satisfied but there is one unassigned literal, so we can propagate its value
          int lastIndex = unassignedLiteralIndex(i);
          bool shouldNegate = lastIndex < 0;
          int finalIndex = shouldNegate ? -lastIndex : lastIndex;

          this->assignUnitClause(finalIndex, !shouldNegate);
          changed = true;
        }
      }
    }

    return true;
  }

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
      if (varIdx < mFirstUnknownIndex) {
        mFirstUnknownIndex = varIdx;
      }
      mVariableState[varIdx] = Tribool::Unknown;
      mNumAssignedVariables--;
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
    if (mVariableState[index] == Tribool::Unknown) {
      return true;
    }

    return std::ranges::none_of(mPropagations, [&](std::pair<int, bool>& pair) {
      return pair.first == index && pair.second != value;
    });
  }

  ClauseStatus checkClause(size_t clauseIdx);

  // Fields
  //==----------------------------------------------------------------------==//

  // Clause database
  std::vector<std::vector<int>> mClauses;

  // Internal solver state
  std::vector<Tribool> mVariableState;
  std::vector<std::pair<int, bool>> mDecisions;
  std::vector<size_t> mPropagationIndices;
  std::vector<std::pair<int, bool>> mPropagations;

  size_t mFirstUnknownIndex = 0;
  size_t mNumAssignedVariables = 0;

  int mDecisionLevel = 0;
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
  if (mDecisionLevel == mVariableState.size() - 1) {
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

      bool sucessfulPropagation = this->propagateUnitClause(variableIndex, !shouldNegate);
      if (!sucessfulPropagation) {
        return false;
      }
    }
  }

  return true;
}

Status Solver::check()
{
  if (mClauses.empty()) {
    std::ranges::for_each(mVariableState, [](auto& v) { v = Tribool::True; });
    return Status::Sat;
  }

  // Do some pre-processing: order variables by usage
  std::vector<int> variableUsage(mVariableState.size(), 0);
  for (const auto& clause : mClauses) {
    for (int literal : clause) {
      int index = literal < 0 ? -literal : literal;
      variableUsage[index]++;
    }
  }

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

  // Start search
  std::pair<int, bool> nextState = {1, true};

  while (true) {
    auto [currentIndex, currentValue] = nextState;


    // Check if the current state is okay
    bool shouldBacktrack = false;

    mDecisions.emplace_back(currentIndex, currentValue);
    this->assignVariable(currentIndex, currentValue);
    mDecisionLevel = currentIndex;

    this->pushState();
    if (isValid()) {
      int newState = currentIndex + 1;

      // Is this a complete state?
      if (mDecisions.size() == mVariableState.size() - 1) {
        return Status::Sat;
      }

      if (isValidChoice(newState, true)) {
        nextState = {newState, true};
      } else if (isValidChoice(newState, false)) {
        nextState = {newState, false};
      } else {
        // There is no valid choice for this literal
        this->popState();
        --mNumAssignedVariables;
        shouldBacktrack = true;
      }
    } else if (currentValue == true) {
      this->popState();
      mDecisions.pop_back();
      --mNumAssignedVariables;
      // Try again with setting the current index to false
      nextState = {currentIndex, false};
    } else {
      shouldBacktrack = true;
    }

    assert((nextState != std::make_pair(currentIndex, currentValue)) || shouldBacktrack);

    if (shouldBacktrack) {
      // We will have to backtrack to the closest non-false state
      int i = mDecisions.size() - 1;
      for (; i >= 0; --i) {
        auto [decidedVariable, decidedValue] = mDecisions[i];
        Tribool previousVariableState = mVariableState[decidedVariable];
        mVariableState[decidedVariable] = Tribool::Unknown;
        --mNumAssignedVariables;
        this->popState();
        mDecisions.pop_back();

        if (previousVariableState == Tribool::True && isValidChoice(decidedVariable, false)) {
          nextState = {decidedVariable, false};
          break;
        }
      }

      if (i == -1) {
        return Status::Unsat;
      }
    }
  }
}

std::vector<bool> Solver::model() const
{
  std::vector<bool> result;
  result.push_back(false);
  for (size_t i = 1; i < mVariableState.size(); ++i) {
    assert(mVariableState[i] != Tribool::Unknown);
    result.push_back(mVariableState[i] == Tribool::False);
  }

  return result;
}

std::vector<bool> Instance::model() const
{
  return mModel;
}
