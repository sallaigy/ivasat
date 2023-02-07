#include "ivasat/ivasat.h"

#include <stack>

using namespace ivasat;

namespace
{

enum class Tribool
{
  True,
  False,
  Unknown
};

Tribool operator|(Tribool left, Tribool right)
{
  using enum Tribool;
  if (left == True || right == True) {
    return True;
  }

  if (left == Unknown || right == Unknown) {
    return Unknown;
  }

  return False;
}

Tribool operator&(Tribool left, Tribool right)
{
  using enum Tribool;
  if (left == False || right == False) {
    return False;
  }

  if (left == Unknown || right == Unknown) {
    return Unknown;
  }

  return False;
}

Tribool operator~(Tribool value)
{
  switch (value) {
    case Tribool::True:
      return Tribool::False;
    case Tribool::False:
      return Tribool::True;
    default:
      return Tribool::Unknown;
  }
}

class Solver
{
public:
  explicit Solver(Instance& instance)
    : mInstance(instance), mVariables(instance.numVariables() + 1, Tribool::Unknown)
  {}

  Status check();

private:
  bool isValid();

  /// Returns \p true if the given clause is true or unknown with the current variable substitutions. Otherwise, returns \p false.
  bool checkClause(size_t clauseIdx);

  // Fields
  //==----------------------------------------------------------------------==//
  Instance& mInstance;
  std::vector<Tribool> mVariables;
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
  Tribool result = Tribool::False;

  for (int varIdx : clause) {
    bool shouldNegate;
    int variableIndex;

    if (varIdx < 0) {
      shouldNegate = true;
      variableIndex = -varIdx;
    } else {
      shouldNegate = false;
      variableIndex = varIdx;
    }

    Tribool variableValue;
    if (variableIndex > mCurrentIndex) {
      variableValue = Tribool::Unknown;
    } else if (shouldNegate) {
      variableValue = ~(mVariables[variableIndex]);
    } else {
      variableValue = mVariables[variableIndex];
    }

    result = result | variableValue;
  }

  return result != Tribool::False;
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
  std::stack<std::pair<int, Tribool>> wl;
  wl.emplace(1, Tribool::True);

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
      wl.emplace(newState, Tribool::True);
    } else if (currentValue == Tribool::True) {
      // Try again with setting the current index to false
      wl.emplace(currentIndex, Tribool::False);
    } else {
      // We will have to backtrack to the closest non-false state
      int curr = prevIndex;
      while (curr > 0 && mVariables[curr] == Tribool::False) {
        --curr;
      }

      if (curr == 0) {
        // We reached back to the top, the instance is not satisfiable
        return Status::Unsat;
      }

      mCurrentIndex = curr - 1;
      wl.emplace(curr, Tribool::False);
    }
  }

  return Status::Unknown;
}
