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

  solver.dumpStats(std::cout);

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

  this->resetWatches();

  // Find unused variables and set them to true
  std::vector<int> usages(mVariableState.size(), 0);
  for (const Clause& clause : mClauses) {
    for (Literal lit : clause) {
      usages[lit.index()] += 1;
    }
  }

  for (int i = 1; i < usages.size(); ++i) {
    if (usages[i] == 0) {
      this->assignVariable(Literal{i, true});
    }
  }
}

Status Solver::check()
{
  if (mClauses.empty()) {
    std::ranges::for_each(mVariableState, [](auto& v) { v = Tribool::True; });
    return Status::Sat;
  }

  this->preprocess();

  if (bool propagationResult = this->simplify(); !propagationResult) {
    return Status::Unsat;
  } else if (numAssigned() == mVariableState.size() - 1) {
    return Status::Sat;
  }

  // Start search
  Literal nextDecision(pickDecisionVariable(), true);

  while (true) {
    // Check if the current state is okay
    this->pushDecision(nextDecision);

    mStats.decisions++;
    if (numAssigned() == mVariableState.size() - 1) {
      mStats.checkedFullCombinations++;
    }

    bool successfulPropagation = this->propagate();
    if (successfulPropagation) {
      // Is this a complete state?
      if (numAssigned() == mVariableState.size() - 1) {
        return Status::Sat;
      }

      int decisionVariable = pickDecisionVariable();
      nextDecision = {decisionVariable, true};
    } else {
      // We learned a new clause, check the backtracking level
      Clause& learnedClause = mClauses.back();
      int backtrackLevel = -1;
      if (learnedClause.size() == 1) {
        // If a unit clause is learned, we want to jump back to the top level and propagate it.
        backtrackLevel = 1;
      } else {
        for (Literal lit: learnedClause) {
          if (lit.index() != mDecisions.back().index()) {
            backtrackLevel =
            backtrackLevel >= mAssignedAtLevel[lit.index()] ? backtrackLevel : mAssignedAtLevel[lit.index()];
          }
        }
      }

      if (backtrackLevel != -1) {
        this->popDecisionUntil(backtrackLevel);
      }
      bool hasNextState = false;
      for (auto it = mDecisions.rbegin(); it != mDecisions.rend(); ++it) {
        int decidedVariable = it->index();
        Tribool previousVariableState = mVariableState[decidedVariable];
        this->popDecision();

        if (decisionLevel() == 0) {
          // If we backtracked back to the top level, try to simplify the clause database.
          if (bool simplifyResult = this->simplify(); !simplifyResult) {
            return Status::Unsat;
          } else if (numAssigned() == mVariableState.size() - 1) {
            return Status::Sat;
          }

          int newDecisionVariable = pickDecisionVariable();
          nextDecision = {newDecisionVariable, true};
          hasNextState = true;
          break;
        }

        bool possibleValue = previousVariableState != Tribool::True;
        if (previousVariableState == Tribool::True && isValidChoice(decidedVariable, possibleValue)) {
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
  std::deque<int> queue;
  if (mDecisions.empty()) {
    // If we are propagating top level, we want to check all clauses
    queue.emplace_back(0);
  } else {
    queue.emplace_back(mDecisions.back().index());
  }

  while (!queue.empty()) {
    int lastAssigned = queue.front();
    const std::vector<int>& clausesToCheck = mWatches[lastAssigned];
    queue.pop_front();
    for (int i : clausesToCheck) {
      const auto& clause = mClauses[i];
      auto clauseStatus = checkClause(clause);
      if (clauseStatus == ClauseStatus::Conflicting) {
        mStats.conflicts++;
        this->analyzeConflict(i);
        return false;
      }

      if (clauseStatus == ClauseStatus::Unit) {
        // The clause is not satisfied but there is one unassigned literal, so we can propagate its value
        Literal lastLiteral = unassignedLiteral(clause);
        this->assignUnitClause(lastLiteral, i);
        queue.emplace_back(lastLiteral.index());
      }
    }
  }

  return true;
}

void Solver::analyzeConflict(int conflictClauseIndex)
{
  // Find a cut of the implication graph through a unique implication point (UIP).
  // The UIP is a node at decision level `d` such that every path from the decision variable at level `d` to the
  // conflict node must go through it.

  // A cut for a UIP `l` is a pair (A,B) where
  //  - B contains all successors of `l` where there is a path to the conflict node
  //  - A contains all the rest of nodes

  // TODO: There is a more sophisticated linear-time algorithm described in the Minisat paper
  // If we are propagating top-level, there is no last decision
  if (mDecisions.empty()) {
    return;
  }

  std::vector<Literal> newClause = this->lastUniqueImplicationPointCut(conflictClauseIndex);
  if (!newClause.empty()) {
    mStats.learnedClauses++;
    std::ranges::sort(newClause);
    newClause.erase(std::unique(newClause.begin(), newClause.end()), newClause.end());

    mClauses.emplace_back(newClause);
    for (Literal lit : newClause) {
      mWatches[lit.index()].push_back(static_cast<int>(mClauses.size() - 1));
    }
    mWatches[0].push_back(static_cast<int>(mClauses.size() - 1));

    for (Literal lit : mClauses[conflictClauseIndex]) {
      mActivity[lit.index()] += 1;
    }

    // Decay all activities
    for (int i = 1; i < mActivity.size(); ++i) {
      mActivity[i] *= DefaultActivityDecay;
    }
  }
}

std::vector<Literal> Solver::lastUniqueImplicationPointCut(int conflictClauseIndex)
{
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
    std::vector<Literal> preds = implyingPredecessors(lit);
    for (Literal predecessor : preds) {
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

  return newClause;
}

std::vector<Literal> Solver::implyingPredecessors(Literal lit)
{
  std::vector<Literal> result;

  int literalIndex = lit.index();
  int impliedByClause = mImplications[literalIndex];
  if (impliedByClause == UnknownIndex) {
    return result;
  }

  for (Literal clauseLit : mClauses[impliedByClause]) {
    if (clauseLit.index() != literalIndex) {
      result.emplace_back(clauseLit.index(), mVariableState[clauseLit.index()] == Tribool::True);
    }
  }

  return result;
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
  : mWatches(instance.numVariables() + 1, std::vector<int>{}),
    mVariableState(instance.numVariables() + 1, Tribool::Unknown),
    mActivity(instance.numVariables() + 1, 1.0),
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
  int lastIdx = mTrailIndices.back();
  mTrailIndices.pop_back();

  for (int i = lastIdx; i < mTrail.size(); ++i) {
    int varIdx = mTrail[i].index();
    this->undoAssignment(varIdx);
  }
  mDecisions.pop_back();

  if (!mTrail.empty()) {
    mTrail.erase(mTrail.begin() + lastIdx, mTrail.end());
  }
}

void Solver::popDecisionUntil(int level)
{
  assert(level <= decisionLevel() && "Cannot pop a decision which did not take place");

  size_t decisionsToPop = decisionLevel() - level;
  for (unsigned i = 0; i < decisionsToPop; ++i) {
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
  mStats.propagations++;
  int variableIndex = literal.index();
  assert(mImplications[variableIndex] == UnknownIndex && "No implications should exists for a freshly assigned unit clause");

  this->assignVariable(literal);
  mImplications[variableIndex] = clauseIndex;
}

bool Solver::simplify()
{
  assert(mDecisions.empty() && "Simplification should only be called on the top level!");

  if (!this->propagate()) {
    return false;
  }

  // Delete all clauses which are true
  mClauses.erase(std::remove_if(mClauses.begin(), mClauses.end(), [this](const Clause& clause) {
    return std::ranges::any_of(clause, [this](Literal lit) {
      return mVariableState[lit.index()] == liftBool(lit.value());
    });
  }), mClauses.end());

  // Remove all false literals from clauses
  for (Clause& clause : mClauses) {
    clause.remove([this](Literal lit) {
      Tribool assignedValue = mVariableState[lit.index()];
      return assignedValue != Tribool::Unknown && liftBool(lit.value()) != assignedValue;
    });
  }

  assert(std::ranges::none_of(mClauses, [](Clause& c) { return c.size() == 0; })
    && "There should be no empty clauses left after simplification!");

  this->resetWatches();

  return true;
}

void Solver::resetWatches()
{
  std::ranges::for_each(mWatches, [](std::vector<int>& v) {
    v.clear();
  });

  mWatches[0].reserve(mClauses.size());
  for (int i = 0; i < mClauses.size(); ++i) {
    for (Literal lit : mClauses[i]) {
      mWatches[lit.index()].push_back(i);
    }
    mWatches[0].push_back(i);
  }
}

int Solver::pickDecisionVariable() const
{
  double maxActivity = -1.0;
  int maxActivityIndex = UnknownIndex;
  for (int i = 1; i < mVariableState.size(); ++i) {
    if (mVariableState[i] != Tribool::Unknown) {
      continue;
    }

    if (mActivity[i] > maxActivity) {
      maxActivity = mActivity[i];
      maxActivityIndex = i;
    }
  }

  assert(maxActivityIndex != -1 && "There must be an unassigned index in a valid solver state!");
  return maxActivityIndex;
}

std::vector<bool> Instance::model() const
{
  return mModel;
}
