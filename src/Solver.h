#ifndef IVA_SAT_SOLVER_H
#define IVA_SAT_SOLVER_H

#include <vector>
#include <algorithm>
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

  auto operator<=>(const Literal& other) const = default;

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


  [[nodiscard]] Literal negate() const
  {
    return Literal(-mData);
  }

private:
  int mData;
};

class Clause
{
public:
  explicit Clause(std::vector<Literal> literals)
    : mLiterals(std::move(literals))
  {
    std::ranges::sort(mLiterals);
  }

  Clause(const Clause&) = default;
  Clause& operator=(const Clause&) = default;

  Literal& operator[](int index)
  {
    return mLiterals[index];
  }

  // Iterator support
  using const_iterator = std::vector<Literal>::const_iterator;
  const_iterator begin() const
  {
    return mLiterals.begin();
  }
  const_iterator end() const
  {
    return mLiterals.end();
  }
  unsigned size() const
  {
    return mLiterals.size();
  }

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
