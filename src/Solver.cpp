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

bool Solver::preprocess()
{
  // Order clauses by size
  std::ranges::sort(mClauses, [](auto& l, auto& r) {
    return l.size() < r.size();
  });

  // Find unused variables and set them to true
  std::vector<int> usages(mVariableState.size(), 0);
  for (const Clause& clause : mClauses) {
    for (Literal lit : clause) {
      usages[lit.index()] += 1;
    }
  }

  for (int i = 1; i < usages.size(); ++i) {
    if (usages[i] == 0) {
      this->enqueue(Literal{i, true});
    }
  }

  // Learn unit clauses as facts
  for (Clause& clause : mClauses) {
    if (clause.size() == 0) {
      return false;
    }

    if (clause.size() == 1) {
      Literal literal = clause[0];
      if (mVariableState[literal.index()] == Tribool::Unknown) {
        this->enqueue(literal);
      } else if (mVariableState[literal.index()] != liftBool(literal.value())) {
        // Conflicting assignment, the instance is unsat
        return false;
      }
    }
  }

  this->resetWatches();

  return true;
}

Status Solver::check()
{
  if (mClauses.empty()) {
    std::ranges::for_each(mVariableState, [](auto& v) { v = Tribool::True; });
    return Status::Sat;
  }

  if (!this->preprocess()) {
    return Status::Unsat;
  }

  // Start search
  while (true) {
    int conflictClause = this->propagate();
    if (conflictClause != UnknownIndex) {
      mStats.conflicts++;

      if (decisionLevel() == 0) {
        return Status::Unsat;
      }

      // We reached a conflict, perform backtracking
      int backtrackLevel = this->analyzeConflict(conflictClause);
      this->popDecisionUntil(backtrackLevel);
      this->assignUnitClause(mClauses.back().back(), mClauses.size() - 1);
    } else {
      // Is this a complete state?
      if (numAssigned() == mVariableState.size() - 1) {
        return Status::Sat;
      }

      if (decisionLevel() == 0) {
        this->simplify();
      }

      int decisionVariable = pickDecisionVariable();
      Literal nextDecision = {decisionVariable, true};
      this->pushDecision(nextDecision);
    }
  }
}

int Solver::propagate()
{
  while (!mQueue.empty()) {
    int lastAssigned = mQueue.front();
    assert(lastAssigned != 0);

    std::vector<Watch>& watchers = mWatches[lastAssigned];
    mQueue.pop_front();
    /*
     1. If the other watched literal is true, do nothing.
     2. If one of the unwatched literals L′ is not false, restore
        the invariant by updating the clause so that it watches L′ instead of −L.
     3. Otherwise, consider the other watched literal L′ in the
        clause:
     3.1. If it is not set, propagate L′.
     3.2. Otherwise, L′ is false, and we have found a conflict.
    */
    auto watchIt = watchers.begin();
    while (watchIt != watchers.end()) {
      Watch& watch = *watchIt;

      int clauseIndex = watch.clauseIdx;
      Clause& clause = mClauses[clauseIndex];
      assert(mVariableState[watch.lit.index()] != Tribool::Unknown);

      Literal& first = clause[0];
      Literal& second = clause[1];

      if (value(first) == Tribool::True || value(second) == Tribool::True) {
        // The first watch is true, the clause is satisfied
        ++watchIt;
        continue;
      }

      assert(lastAssigned == first.index() || lastAssigned == second.index());
      if (lastAssigned == first.index() && value(first) == Tribool::False) {
        // Find another watch
        int newWatchIdx = clause.size();
        if (clause.size() > 2) {
          newWatchIdx = 2;
          while (newWatchIdx < clause.size() && value(clause[newWatchIdx]) != Tribool::Unknown) {
            newWatchIdx++;
          }
        }

        if (newWatchIdx == clause.size()) {
          if (value(second) == Tribool::Unknown) {
            // If there is no possible new watch and the second watch is unassigned, it should be propagated.
            this->assignUnitClause(second, clauseIndex);
          } else {
            // The second watch is false and there are no other possible watches, the clause is conflicting.
            mQueue.clear();
            return clauseIndex;
          }
        } else {
          Literal watchedLit = clause[newWatchIdx];
          std::swap(first, clause[newWatchIdx]);
          watchIt = watchers.erase(watchIt);
          mWatches[watchedLit.index()].emplace_back(clauseIndex, watchedLit);
          continue;
        }
      } else if (lastAssigned == second.index() && value(second) == Tribool::False) {
        // Find another watch
        int newWatchIdx = clause.size();
        if (clause.size() > 2) {
          newWatchIdx = 2;
          while (newWatchIdx < clause.size() && value(clause[newWatchIdx]) != Tribool::Unknown) {
            newWatchIdx++;
          }
        }

        if (newWatchIdx == clause.size()) {
          if (value(first) == Tribool::Unknown) {
            // If there is no possible new watch and the second watch is unassigned, it should be propagated.
            this->assignUnitClause(first, clauseIndex);
          } else {
            // The second watch is false and there are no other possible watches, the clause is conflicting.
            mQueue.clear();
            return clauseIndex;
          }
        } else {
          Literal watchedLit = clause[newWatchIdx];
          std::swap(second, clause[newWatchIdx]);
          watchIt = watchers.erase(watchIt);
          mWatches[watchedLit.index()].emplace_back(clauseIndex, watchedLit);
          continue;
        }
      }
      ++watchIt;
    }
  }

  return UnknownIndex;
}

int Solver::analyzeConflict(int conflictClauseIndex)
{
  // Find a cut of the implication graph through a unique implication point (UIP).
  // The UIP is a node at decision level `d` such that every path from the decision variable at level `d` to the
  // conflict node must go through it.

  // A cut for a UIP `l` is a pair (A,B) where
  //  - B contains all successors of `l` where there is a path to the conflict node
  //  - A contains all the rest of nodes

  std::vector<Literal> newClause;
  int backtrackLevel = this->firstUniqueImplicationPointCut(conflictClauseIndex, newClause);

  mClauses.emplace_back(newClause, true);
  mStats.learnedClauses++;
  if (newClause.size() >= 2) {
    this->watchClause(mClauses.size() - 1);
  }

  // Decay all activities
  for (int i = 1; i < mActivity.size(); ++i) {
    mActivity[i] *= DefaultActivityDecay;
  }

  // Bump activity of related variables
  for (Literal lit : newClause) {
    mActivity[lit.index()] += 1;
  }

  return backtrackLevel;
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
int Solver::firstUniqueImplicationPointCut(int conflictClauseIndex, std::vector<Literal>& newClause)
{
  // Track the variables
  std::vector<bool> seen(mVariableState.size(), false);

  int counter = 0;
  size_t trailIdx = mTrail.size() - 1;

  newClause.clear();
  int backtrackLevel = 0;

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
        backtrackLevel = std::max(backtrackLevel, mAssignedAtLevel[lit.index()]);
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
      return backtrackLevel;
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

int Solver::backtrack()
{
  // We learned a new clause, check the backtracking level
  const Clause& learnedClause = mClauses.back();
  if (learnedClause.size() == 1) {
    // If a unit clause is learned, we want to jump back to the top level and propagate it.
    this->popDecisionUntil(0);
    return learnedClause.back().index();
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
    this->popDecisionUntil(backtrackLevel - 1);
  }

  return learnedClause.back().index();
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

void Solver::enqueue(Literal literal)
{
  this->assignVariable(literal);
  mQueue.emplace_back(literal.index());
}

Solver::Solver(const Instance& instance)
  : mWatches(instance.numVariables() + 1, std::vector<Watch>{}),
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
  mStats.decisions++;
  mTrailIndices.emplace_back(mTrail.size());
  mDecisions.emplace_back(literal);
  this->enqueue(literal);
}

void Solver::assignUnitClause(Literal literal, int clauseIndex)
{
  mStats.propagations++;
  int variableIndex = literal.index();
  assert(mImplications[variableIndex] == UnknownIndex && "No implications should exists for a freshly assigned unit clause");

  mImplications[variableIndex] = clauseIndex;
  this->enqueue(literal);
}

void Solver::simplify()
{
  assert(mDecisions.empty() && "Simplification should only be called on the top level!");

  auto first = std::remove_if(mClauses.begin(), mClauses.end(), [this](const Clause& clause) {
    // Delete all clauses which are true
    return std::ranges::any_of(clause, [this](Literal lit) {
      return mVariableState[lit.index()] == liftBool(lit.value());
    });
  });
  long numEliminated = std::distance(first, mClauses.end());
  mStats.clausesEliminatedBySimplification += numEliminated;
  mClauses.erase(first, mClauses.end());

  // Remove all false literals from clauses
  for (Clause& clause : mClauses) {
    long numRemoved = clause.remove([this](Literal lit) {
      Tribool assignedValue = mVariableState[lit.index()];
      return assignedValue != Tribool::Unknown && liftBool(lit.value()) != assignedValue;
    });
  }

  assert(std::ranges::none_of(mClauses, [](Clause& c) { return c.size() == 0; })
    && "There should be no empty clauses left after simplification!");

  // Deleting clauses changed clause indices: re-initialize watches and reset the implications graph.
  this->resetWatches();
  std::ranges::fill(mImplications, UnknownIndex);
}

void Solver::resetWatches()
{
  std::ranges::for_each(mWatches, [](std::vector<Watch>& v) {
    v.clear();
  });

  for (int clauseIdx = 0; clauseIdx < mClauses.size(); ++clauseIdx) {
    this->watchClause(clauseIdx);
  }
}

void Solver::watchClause(int clauseIdx)
{
  Clause& clause = mClauses[clauseIdx];
  if (clause.size() < 2) {
    return;
  }

  assert(clause.size() >= 2 && "Unit clauses should have been propagated earlier!");

//  int first = 0;
//  while (first < clause.size() - 1 && mVariableState[clause[first].index()] != Tribool::Unknown) {
//    first++;
//  }
//
//  int second = first + 1;
//
//  assert(second != clause.size() && "No suitable watch for clause!");
//  while (second < clause.size() - 1 && mVariableState[clause[first].index()] != Tribool::Unknown) {
//    second++;
//  }
//
//  std::swap(clause[0], clause[first]);
//  std::swap(clause[1], clause[second]);

  mWatches[clause[0].index()].emplace_back(clauseIdx, clause[0]);
  mWatches[clause[1].index()].emplace_back(clauseIdx, clause[1]);
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

Tribool Solver::value(Literal literal)
{
  if (mVariableState[literal.index()] == Tribool::Unknown) {
    return Tribool::Unknown;
  }

  return liftBool(mVariableState[literal.index()] == liftBool(literal.value()));
}

std::vector<bool> Instance::model() const
{
  return mModel;
}
