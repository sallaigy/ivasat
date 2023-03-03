#ifndef IVA_SAT_SOLVER_H
#define IVA_SAT_SOLVER_H

#include <vector>
#include <cassert>


namespace ivasat
{

class Literal
{
public:
  explicit Literal(int data)
    : mData(data)
  {
    assert(data != 0 && "Literal data must be strictly positive or negative!");
  }

  Literal(int index, bool value)
    : mData(value ? index : -index)
  {
    assert(index > 0 && "A literal cannot have a zero or negative index!");
  }

  Literal(const Literal&) = default;
  Literal& operator=(const Literal&) = default;

  [[nodiscard]] int index() const
  {
    return isNegated() ? -mData : mData;
  }

  [[nodiscard]] bool value() const
  {
    return !isNegated();
  }

  [[nodiscard]] bool isNegated() const
  {
    return mData < 0;
  }

private:
  int mData;
};

class Clause
{
public:
  Clause(const Clause&) = delete;
  Clause& operator=(const Clause&) = delete;



private:
  std::vector<Literal> mLiterals;
};

enum class Tribool
{
  False,
  True,
  Unknown
};

Tribool operator&(Tribool left, Tribool right);
Tribool operator|(Tribool left, Tribool right);
Tribool operator~(Tribool value);

} // namespace ivasat

#endif //IVA_SAT_SOLVER_H
