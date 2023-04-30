#include "Solver.h"

#include <set>
#include <algorithm>
#include <iostream>
#include <cassert>

using namespace ivasat;

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
  Literal nextDecision(1, true);

  while (true) {
    // Check if the current state is okay
    this->pushDecision(nextDecision);

    mStats.checkedStates++;
    if (numAssigned() == mVariableState.size() - 1) {
      mStats.checkedFullCombinations++;
    }

    bool successfulPropagation = this->propagate();
    if (successfulPropagation) {
      // Is this a complete state?
      if (numAssigned() == mVariableState.size() - 1) {
        return Status::Sat;
      }

      int decisionVariable = pickDecisionVariable(nextDecision.index());
      nextDecision = {decisionVariable, true};
    } else {
      // Backtrack to the closest non-false state
      bool hasNextState = false;
      for (auto it = mDecisions.rbegin(); it != mDecisions.rend(); ++it) {
        int decidedVariable = it->index();
        Tribool previousVariableState = mVariableState[decidedVariable];
        this->popDecision();

        if (previousVariableState == Tribool::True && isValidChoice(decidedVariable, false)) {
          nextDecision = {decidedVariable, false};
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

bool Solver::propagate()
{
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
        Literal lastLiteral = unassignedLiteral(clause);
        this->assignUnitClause(lastLiteral, i);
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

void Solver::assignVariable(Literal literal)
{
  int variableIndex = literal.index();
  Tribool value = liftBool(literal.value());
  assert(mVariableState[variableIndex] == Tribool::Unknown && "Can only assign a previously unset variable!");

  mVariableState[variableIndex] = value;

  assert(mAssignedAtLevel[variableIndex] == UnknownIndex && "No assignment level should exist for an unassigned variable");
  mAssignedAtLevel[variableIndex] = this->decisionLevel();
  mTrail.push_back(literal);
}

Solver::Solver(const Instance& instance)
  : mVariableState(instance.numVariables() + 1, Tribool::Unknown),
    mImplications(instance.numVariables() + 1, UnknownIndex),
    mAssignedAtLevel(instance.numVariables() + 1, UnknownIndex)
{
  mClauses.reserve(instance.clauses().size());
  for (const auto& clauseData : instance.clauses()) {
    std::vector<Literal> literals;
    for (int litData : clauseData) {
      literals.emplace_back(litData);
    }
    mClauses.emplace_back(literals);
  }
}

void Solver::popDecision()
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

void Solver::popDecisionUntil(int varIdx)
{
  int assignedAt = mAssignedAtLevel[varIdx];
  assert(assignedAt != UnknownIndex && "Cannot pop a decision which did not take place");
  assert(assignedAt <= decisionLevel() && "Cannot pop a decision which did not take place");

  size_t decisionsToPop = decisionLevel() - assignedAt;
  for (unsigned i = 0; i <= decisionsToPop; ++i) {
    this->popDecision();
  }
}

void Solver::undoAssignment(size_t variableIndex)
{
  assert(mVariableState[variableIndex] != Tribool::Unknown && "Cannot undo an assignment that did not take place");

  mVariableState[variableIndex] = Tribool::Unknown;
  mAssignedAtLevel[variableIndex] = UnknownIndex;
  mImplications[variableIndex] = UnknownIndex;
}

void Solver::pushDecision(Literal literal)
{
  mTrailIndices.emplace_back(mTrail.size());
  mDecisions.emplace_back(literal);
  this->assignVariable(literal);
}

void Solver::assignUnitClause(Literal literal, int clauseIndex)
{
  int variableIndex = literal.index();
  assert(mImplications[variableIndex] == UnknownIndex && "No implications should exists for a freshly assigned unit clause");

  this->assignVariable(literal);
  mImplications[variableIndex] = clauseIndex;
}

int Solver::pickDecisionVariable(int start) const
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

std::vector<bool> Instance::model() const
{
  return mModel;
}
