#include "Solver.h"

#include <boost/dynamic_bitset.hpp>

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
      // We reached a conflict, perform backtracking
      this->backtrack();

      bool hasNextState = false;
      for (auto it = mDecisions.rbegin(); it != mDecisions.rend(); ++it) {
        int decidedVariable = it->index();
        Tribool previousVariableState = mVariableState[decidedVariable];
        this->popDecision();

        if (decisionLevel() == 0) {
          mStats.restarts += 1;
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

  std::vector<Literal> newClause = this->firstUniqueImplicationPointCut(conflictClauseIndex);
  if (!newClause.empty()) {
    mStats.learnedClauses++;
    std::ranges::sort(newClause);
    newClause.erase(std::unique(newClause.begin(), newClause.end()), newClause.end());

    mClauses.emplace_back(newClause, true);
    for (Literal lit : newClause) {
      mWatches[lit.index()].push_back(static_cast<int>(mClauses.size() - 1));
    }
    mWatches[0].push_back(static_cast<int>(mClauses.size() - 1));

    // Decay all activities
    for (int i = 1; i < mActivity.size(); ++i) {
      mActivity[i] *= DefaultActivityDecay;
    }

    // Bump activity of related variables
    for (Literal lit : newClause) {
      mActivity[lit.index()] += 1;
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
    std::vector<Literal> preds;
    fillImplyingPredecessors(lit, preds);
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

// Linear time algorithm to find a 1-UIP cut, adapted from the algorithm described in the Minisat paper.
//
// Given an implication graph, a unique implication point is a node at decision level `d` such that every path from the decision variable
// at level `d` to the conflict node must go through it. In other words, the UIP is a dominator in the implication graph. The first unique
// implication point (1-UIP) is the dominator closest to the conflict.
//
// A cut for a UIP `l` is a pair (R,C) where
//  - C contains all successors of `l` where there is a path to the conflict node, and
//  - R contains all the rest of the nodes.
// The new clause contains the negation of literals that have edges from the predecessors side (R) to the conflict side (C).
//
// The basic idea of the algorithm is to perform a backwards breadth-first traversal on the implication graph, until we find the first UIP.
std::vector<Literal> Solver::firstUniqueImplicationPointCut(int conflictClauseIndex)
{
  // Track the variables
  std::vector<bool> seen(mVariableState.size(), false);

  int counter = 0;
  size_t trailIdx = mTrail.size() - 1;

  std::vector<Literal> newClause;

  // Track the predecessors of the currently processed literal. In the first step, we start from the conflict node,
  // so we start with its predecessor set, i.e. the literals of the conflict clause.
  const Clause& conflictClause = mClauses[conflictClauseIndex];
  std::vector<Literal> predecessors;
  predecessors.reserve(conflictClause.size());

  for (Literal lit : conflictClause) {
    predecessors.emplace_back(lit.index(), mVariableState[lit.index()] == Tribool::True);
  }

  while (true) {
    for (Literal lit : predecessors) {
      if (seen[lit.index()]) {
        continue;
      }

      seen[lit.index()] = true;
      if (mAssignedAtLevel[lit.index()] == decisionLevel()) {
        counter++;
      } else if (mAssignedAtLevel[lit.index()] > 0) {
        // If a predecessor literal is from another decision level, it is not a successor of the 1-UIP, so it belongs to the "reason" side in the cut.
        // As the current literal belongs to the conflict side, it means that this literal has an edge from the predecessors side to the conflict side,
        // meaning that it has to be included in the learned clause.
        //
        // We exclude literals from the top level as they were assigned as part of pre-processing and simplification.
        newClause.push_back(lit.negate());
      }
    }

    // Select the next literal to inspect.
    Literal nextLit = mTrail[trailIdx];
    trailIdx--;
    while (!seen[nextLit.index()]) {
      nextLit = mTrail[trailIdx];
      trailIdx--;
    }

    // Update the predecessor set with the literals that led to the unit propagation of the current literal, i.e. the predecessors of the literal in the implication graph.
    predecessors.clear();
    this->fillImplyingPredecessors(nextLit, predecessors);
    assert((counter == 1 || !predecessors.empty()) && "There must be at least one implying predecessor of an implied literal!");

    counter--;
    if (counter == 0) {
      newClause.push_back(nextLit.negate());
      return newClause;
    }
  }
}

void Solver::fillImplyingPredecessors(Literal lit, std::vector<Literal>& result)
{
  int literalIndex = lit.index();
  int impliedByClause = mImplications[literalIndex];
  if (impliedByClause == UnknownIndex) {
    return;
  }

  Clause& implyingClause = mClauses[impliedByClause];

  for (Literal clauseLit : implyingClause) {
    if (clauseLit.index() != literalIndex) {
      result.emplace_back(clauseLit.index(), mVariableState[clauseLit.index()] == Tribool::True);
    }
  }
}

void Solver::backtrack()
{
  // We learned a new clause, check the backtracking level
  const Clause& learnedClause = mClauses.back();
  if (learnedClause.size() == 1) {
    // If a unit clause is learned, we want to jump back to the top level and propagate it.
    this->popDecisionUntil(1);
  }

  // Determine the backtrack level: this should be the second-largest decision level of the literals in the learned clause.
  int backtrackLevel = -1;
  for (Literal lit: learnedClause) {
    if (lit.index() != mDecisions.back().index()) {
      int assignmentLevel = mAssignedAtLevel[lit.index()];
      if (backtrackLevel < assignmentLevel) {
        backtrackLevel = assignmentLevel;
      }
    }
  }

  if (backtrackLevel != -1) {
    this->popDecisionUntil(backtrackLevel);
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

  bool changed = true;
  while (changed) {
    changed = false;
    
    if (!this->propagate()) {
      return false;
    }
  
    // Find pure literals
    boost::dynamic_bitset<> positive{mVariableState.size()};
    boost::dynamic_bitset<> negative{mVariableState.size()};
    for (const Clause& clause : mClauses) {
      for (Literal lit : clause) {
        if (lit.isNegated()) {
          negative[lit.index()] = true;
        } else {
          positive[lit.index()] = true;
        }
      }
    }

    for (int i = 1; i < mVariableState.size(); ++i) {
      bool isPure = positive[i] ^ negative[i];
      if (isPure && mVariableState[i] == Tribool::Unknown) {
        if (positive[i]) {
          this->assignVariable(Literal{i, true});
        } else if (negative[i]) {
          this->assignVariable(Literal{i, false});
        }
        mStats.pureLiterals++;
      }
    }

    auto first = std::remove_if(mClauses.begin(), mClauses.end(), [this](const Clause& clause) {
      // Delete all clauses which are true
      return std::ranges::any_of(clause, [this](Literal lit) {
        return mVariableState[lit.index()] == liftBool(lit.value());
      });
    });
    long numEliminated = std::distance(first, mClauses.end());
    mStats.clausesEliminatedBySimplification += numEliminated;
    mClauses.erase(first, mClauses.end());
    changed |= numEliminated != 0;

    // Remove all false literals from clauses
    for (Clause& clause : mClauses) {
      long numRemoved = clause.remove([this](Literal lit) {
        Tribool assignedValue = mVariableState[lit.index()];
        return assignedValue != Tribool::Unknown && liftBool(lit.value()) != assignedValue;
      });
      changed |= numRemoved != 0;
    }

    assert(std::ranges::none_of(mClauses, [](Clause& c) { return c.size() == 0; })
      && "There should be no empty clauses left after simplification!");

    // Deleting clauses changed clause indices: re-initialize watches and reset the implications graph.
    this->resetWatches();
    std::ranges::fill(mImplications, UnknownIndex);
  }

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
