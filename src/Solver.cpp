#include "Solver.h"

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
  unsigned learnedClauses = 0;
};

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
    : mVariableState(instance.numVariables() + 1, Tribool::Unknown),
    mImplications(instance.numVariables() + 1, UnknownIndex), mAssignedAtLevel(instance.numVariables() + 1, UnknownIndex)
  {
    for (const auto& clauseData : instance.clauses()) {
      std::vector<Literal> literals;
      for (int litData : clauseData) {
        literals.emplace_back(litData);
      }
      mClauses.emplace_back(literals);
    }
  }

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
      int varIdx = mTrail[i].index();
      this->undoAssignment(varIdx);
    }
    mDecisions.pop_back();

    if (!mTrail.empty()) {
      mTrail.erase(mTrail.begin() + lastIdx, mTrail.end());
    }
  }

  Literal unassignedLiteral(size_t clauseIdx)
  {
    for (Literal literal : mClauses[clauseIdx]) {
      auto currentValue = mVariableState[literal.index()];
      if (currentValue == Tribool::Unknown) {
        return literal;
      }
    }

    assert(false && "Should be unreachable!");
    return Literal{0};
  }

private:
  bool isValid();

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
  std::cout << "Learned clauses: " << solver.statistics().learnedClauses << "\n";

  if (status == Status::Sat) {
    mModel = solver.model();
  }

  return status;
}

Solver::ClauseStatus Solver::checkClause(const Clause& clause)
{
  ClauseStatus status = ClauseStatus::Conflicting;

  for (Literal literal : clause) {
    Tribool variableValue = Tribool::Unknown;
    if (mVariableState[literal.index()] == Tribool::Unknown) {
      if (status == ClauseStatus::Unit || status == ClauseStatus::Unresolved) {
        status = ClauseStatus::Unresolved;
        continue;
      } else {
        status = ClauseStatus::Unit;
        continue;
      }
    } else {
      variableValue = mVariableState[literal.index()];
      variableValue = literal.isNegated() ? ~variableValue : variableValue;
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
      Literal lastLiteral = unassignedLiteral(i);

      bool sucessfulPropagation = this->propagateUnitClause(lastLiteral.index(), lastLiteral.value(), i);
      if (!sucessfulPropagation) {
        return false;
      }
    }
  }

  return true;
}

void Solver::preprocess()
{
  // Order clauses by size
  std::ranges::sort(mClauses, [](auto& l, auto& r) {
    return l.size() < r.size();
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
        int decidedVariable = it->index();
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
        Literal lastLiteral = unassignedLiteral(i);
        this->assignUnitClause(lastLiteral.index(), lastLiteral.value(), i);
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

  // TODO: There is a more sophisticated linear-time algorithm described in the Minisat paper

  auto preds = [this](Literal lit) {
    std::vector<Literal> result;

    int literalIndex = lit.index();
    int impliedByClause = mImplications[literalIndex];
    if (impliedByClause == UnknownIndex) {
      return result;
    }

    for (Literal clauseLit : mClauses[impliedByClause]) {
      if (clauseLit.index() != literalIndex) {
        result.emplace_back(clauseLit.index(), mVariableState[clauseLit.index()] == Tribool::True ? true : false);
      }
    }

    return result;
  };

  // We are performing a last UIP cut, meaning that the reason side will contain the last decision literal and all literals
  // which were assigned on previous decision levels. The conflict side will contain all implied literals of the current
  // decision level.
  Literal lastDecision = mDecisions.back();

  std::vector<Literal> reason;
  std::vector<Literal> conflict;

  std::ranges::partition_copy(mTrail, std::back_inserter(conflict), std::back_inserter(reason), [this, lastDecision](Literal lit) {
    return mAssignedAtLevel[lit.index()] == this->decisionLevel() && lastDecision != lit;
  });

  std::vector<Literal> newClause;

  for (Literal lit : conflict) {
    for (Literal predecessor : preds(lit)) {
      if (auto it = std::ranges::find(reason, predecessor); it != reason.end()) {
        newClause.push_back(it->negate());
      }
    }
  }

  // Also add the predecessors of the "conflict" node
  for (Literal conflictLit : mClauses[conflictClauseIndex]) {
    if (auto it = std::ranges::find_if(reason, [conflictLit](Literal l) { return l.index() == conflictLit.index();}); it != reason.end()) {
      newClause.push_back(it->negate());
    }
  }

  if (!newClause.empty()) {
    mStats.learnedClauses++;
    std::ranges::sort(newClause);
    auto last = std::unique(newClause.begin(), newClause.end());
    newClause.erase(last, newClause.end());

    mClauses.emplace_back(newClause);
  }
}

void Solver::dumpImplicationGraph(int conflictClauseIndex)
{
  const auto& conflictClause = mClauses[conflictClauseIndex];
  std::stringstream ss;

  ss << "digraph G {\n";

  for (Literal lit : mTrail) {
    int varIdx = lit.index();

    int assignedAt = mAssignedAtLevel[varIdx];
    ss << "node_" << varIdx << " [label=\"" << varIdx << ":" << std::boolalpha << lit.value() << "@" << assignedAt << "\"];\n";
  }

  for (int i = 0; i < mImplications.size(); ++i) {
    int clauseIdx = mImplications[i];

    if (clauseIdx == UnknownIndex) {
      continue;
    }

    for (Literal lit : mClauses[clauseIdx]) {
      if (lit.index() != i) {
        ss << "node_" << lit.index() << " -> " << "node_" << i << "[label=\"  " << clauseIdx << "\"];\n";
      }
    }
  }

  for (Literal lit : conflictClause) {
    ss << "node_" << lit.index() << " -> " << "conflict[label=\"" << conflictClauseIndex << "\"];\n";
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
