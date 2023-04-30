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