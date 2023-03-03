#include "Solver.h"

using namespace ivasat;

Tribool ivasat::operator&(Tribool left, Tribool right)
{
  if (left == Tribool::False || right == Tribool::False) {
    return Tribool::False;
  }

  if (left == Tribool::Unknown || right == Tribool::Unknown) {
    return Tribool::Unknown;
  }

  return Tribool::True;
}

Tribool ivasat::operator|(Tribool left, Tribool right)
{
  if (left == Tribool::True || right == Tribool::True) {
    return Tribool::True;
  }

  if (left == Tribool::Unknown || right == Tribool::Unknown) {
    return Tribool::Unknown;
  }

  return Tribool::False;
}

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
