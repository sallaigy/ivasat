#include "ivasat/ivasat.h"

#include <stack>

using namespace ivasat;

namespace
{

class Solver
{
public:
  explicit Solver(Instance& instance)
    : mInstance(instance), mVariables(instance.numVariables() + 1, false)
  {}

  Status check();

private:
  bool isValid();

  /// Returns \p true if the given clause is true or unknown with the current variable substitutions. Otherwise, returns \p false.
  bool checkClause(size_t clauseIdx);

  // Fields
  //==----------------------------------------------------------------------==//
  Instance& mInstance;
  std::vector<bool> mVariables;
  int mCurrentIndex = 0;
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
  return Solver{*this}.check();
}

bool Solver::checkClause(size_t clauseIdx)
{
  auto& clause = mInstance.clauses()[clauseIdx];
  bool hasUnknown = false;

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

    if (finalIndex > mCurrentIndex) {
      hasUnknown = true;
      continue;
    }

    bool variableValue;
    if (shouldNegate) {
      variableValue = !(mVariables[finalIndex]);
    } else {
      variableValue = mVariables[finalIndex];
    }

    if (variableValue == true) {
      return true;
    }
  }

  return hasUnknown;
}

bool Solver::isValid()
{
  for (size_t i = 0; i < mInstance.clauses().size(); ++i) {
    if (!checkClause(i)) {
      return false;
    }
  }

  return true;
}

Status Solver::check()
{
  // Start search
  std::stack<std::pair<int, bool>> wl;
  wl.emplace(1, true);

  while (!wl.empty()) {
    auto [currentIndex, currentValue] = wl.top();
    wl.pop();

    // Is this a complete state?
    if (currentIndex == mVariables.size()) {
      return Status::Sat;
    }

    // Check if the current state is okay
    int prevIndex = mCurrentIndex;
    mVariables[currentIndex] = currentValue;
    mCurrentIndex = currentIndex;

    if (isValid()) {
      int newState = currentIndex + 1;
      wl.emplace(newState, true);
    } else if (currentValue == true) {
      // Try again with setting the current index to false
      wl.emplace(currentIndex, false);
    } else {
      // We will have to backtrack to the closest non-false state
      int curr = prevIndex;
      while (curr > 0 && mVariables[curr] == false) {
        --curr;
      }

      if (curr == 0) {
        // We reached back to the top, the instance is not satisfiable
        return Status::Unsat;
      }

      mCurrentIndex = curr - 1;
      wl.emplace(curr, false);
    }
  }

  return Status::Unknown;
}
