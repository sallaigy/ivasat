#include "ivasat/ivasat.h"

#include <stack>
#include <unordered_map>
#include <algorithm>
#include <iostream>
#include <optional>
#include <cassert>

using namespace ivasat;

namespace
{

struct Statistics
{
  unsigned checkedStates = 0;
  unsigned checkedFullCombinations = 0;
};


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
    : mVariables(instance.numVariables() + 1, false), mClauses(instance.clauses())
  {}

  Status check();

  std::vector<bool> model() const;

  const Statistics& statistics() const
  {
    return mStats;
  }

  void learnFact(int variableIndex, bool value)
  {
    assert(!mLearnedFacts.empty());
    mLearnedFacts.back()[variableIndex] = value;
  }

  void pushState()
  {
    mLearnedFacts.emplace_back();
  }

  void popState()
  {
    mLearnedFacts.pop_back();
  }

  std::optional<bool> getLearnedFact(int variableIndex)
  {
    for (auto it = mLearnedFacts.rbegin(), ie = mLearnedFacts.rend(); it != ie; ++it) {
      auto result = it->find(variableIndex);
      if (result != it->end()) {
        return std::make_optional(result->second);
      }
    }

    return std::nullopt;
  }

private:
  bool isValid();

  ClauseStatus checkClause(size_t clauseIdx);

  // Fields
  //==----------------------------------------------------------------------==//
  std::vector<bool> mVariables;
  std::vector<std::vector<int>> mClauses;
  std::vector<std::unordered_map<int, bool>> mLearnedFacts;

  std::vector<int> mReorderedVariables;
  int mCurrentIndex = 0;
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

  mModel = solver.model();

  return status;
}

Solver::ClauseStatus Solver::checkClause(size_t clauseIdx)
{
  const std::vector<int>& clause = mClauses[clauseIdx];

  ClauseStatus status = ClauseStatus::Conflicting;

  for (size_t i = 0; i < clause.size(); ++i) {
    int varIdx = clause[i];

    bool shouldNegate;
    int finalIndex;

    if (varIdx < 0) {
      shouldNegate = true;
      finalIndex = -varIdx;
    } else {
      shouldNegate = false;
      finalIndex = varIdx;
    }

    bool variableValue;
    if (finalIndex > mCurrentIndex) {
      if (auto learnedFact = getLearnedFact(finalIndex); learnedFact) {
        variableValue = shouldNegate != *learnedFact;
      } else if (i == clause.size() - 1 && status != ClauseStatus::Unresolved) {
        return ClauseStatus::Unit;
      } else {
        status = ClauseStatus::Unresolved;
        continue;
      }
    } else {
      variableValue = shouldNegate != (mVariables[finalIndex]);
    }

    if (variableValue == true) {
      return ClauseStatus::Satisfied;
    }
  }

  return status;
}

bool Solver::isValid()
{
  mStats.checkedStates++;
  if (mCurrentIndex == mVariables.size() - 1) {
    mStats.checkedFullCombinations++;
  }

  for (size_t i = 0; i < mClauses.size(); ++i) {
    auto clauseStatus = checkClause(i);
    if (clauseStatus == ClauseStatus::Conflicting) {
      return false;
    }

    if (clauseStatus == ClauseStatus::Unit) {
      // The clause is not satisfied but the last literal is unassigned, so we can propagate its value
      int lastIndex = mClauses[i].back();
      bool shouldNegate = lastIndex < 0;
      int variableIndex = shouldNegate ? -lastIndex : lastIndex;

      this->learnFact(variableIndex, !shouldNegate);
    }
  }

  return true;
}

Status Solver::check()
{
  // Set-up
  this->pushState();

  // Do some pre-processing: order variables by usage
  std::vector<int> variableUsage(mVariables.size(), 0);
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
    return std::ranges::lexicographical_compare(l, r, [](int leftVal, int rightVal) {
      return std::abs(leftVal) < std::abs(rightVal);
    });
  });

  // Start search
  std::pair<int, bool> nextState = {1, true};
  this->pushState();

  while (true) {
    auto [currentIndex, currentValue] = nextState;

    // Is this a complete state?
    if (currentIndex == mVariables.size()) {
      return Status::Sat;
    }

    // Check if the current state is okay
    int prevIndex = mCurrentIndex;
    mVariables[currentIndex] = currentValue;
    mCurrentIndex = currentIndex;

    this->pushState();
    if (isValid()) {
      int newState = currentIndex + 1;
      nextState = {newState, true};
    } else if (currentValue == true) {
      this->popState();
      // Try again with setting the current index to false
      nextState = {currentIndex, false};
    } else {
      // We will have to backtrack to the closest non-false state
      int curr = prevIndex;
      while (curr > 0 && mVariables[curr] == false) {
        --curr;
        this->popState();
      }

      if (curr == 0) {
        // We reached back to the top, the instance is not satisfiable
        return Status::Unsat;
      }

      mCurrentIndex = curr - 1;
      nextState = {curr, false};
    }
  }

  return Status::Unknown;
}

std::vector<bool> Solver::model() const
{
  return mVariables;
}


std::vector<bool> Instance::model() const
{
  return mModel;
}