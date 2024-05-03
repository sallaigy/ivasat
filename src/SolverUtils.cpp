#include "Solver.h"

#include <iostream>
#include <sstream>

using namespace ivasat;

Tribool ivasat::operator~(Tribool value)
{
  if (value == Tribool::True) {
    return Tribool::False;
  }

  if (value == Tribool::False) {
    return Tribool::True;
  }

  return Tribool::Unknown;
}

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

void Solver::dumpStats(std::ostream& os) const
{
  os << "Variables: " << mStats.variables << "\n";
  os << "Clauses: " << mStats.clauses << "\n";
  os << "Decisions: " << mStats.decisions << "\n";
  os << "Conflicts: " << mStats.conflicts << "\n";
  os << "Learned clauses: " << mStats.learnedClauses << "\n";
  os << "Propagations: " << mStats.propagations << "\n";
  os << "Restarts: " << mStats.restarts << "\n";
  os << "Clauses eliminated by simplification: " << mStats.clausesEliminatedBySimplification << "\n";
  os << "Clauses eliminated by activity heuristic: " << mStats.clausesEliminatedByReduce << "\n";
  os << "Pure literals found: " << mStats.pureLiterals << "\n";
}

void Solver::dumpImplicationGraph(int conflictClauseIndex)
{
  const auto& conflictClause = mClauses[conflictClauseIndex];
  std::stringstream ss;

  ss << "digraph G {\n";

  for (Literal lit : mTrail) {
    int varIdx = lit.index();

    int assignedAt = mAssignedAtLevel[varIdx];

    std::string colorLabel;
    if (std::ranges::find(mDecisions, lit) != mDecisions.end()) {
      colorLabel = ", style=filled, fillcolor=\"green\"";
    }

    ss << "node_" << varIdx << " [label=\"" << varIdx << ":" << std::boolalpha << lit.value() << "@" << assignedAt << "\"" << colorLabel << "];\n";
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