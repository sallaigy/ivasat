#ifndef IVA_SAT_CLAUSE_H
#define IVA_SAT_CLAUSE_H

#include <cassert>
#include <vector>
#include <algorithm>

#include "Allocator.h"

namespace ivasat
{

/// Represents a literal inside of a SAT problem, that is a pair of (variable, value).
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
  explicit Clause(std::vector<Literal> literals, bool isLearned = false)
  : mLiterals(std::move(literals)), mIsLearned(isLearned)
  {
    std::ranges::sort(mLiterals);
  }

  Clause(const Clause&) = default;
  Clause& operator=(const Clause&) = default;

  const Literal& operator[](int index) const
  {
    return mLiterals[index];
  }

  bool isLearned() const
  {
    return mIsLearned;
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
  size_t size() const
  {
    return mLiterals.size();
  }

  // Manipulation
  void remove(Literal lit)
  {
    mLiterals.erase(std::remove(mLiterals.begin(), mLiterals.end(), lit), mLiterals.end());
  }

  template<class Predicate>
  long remove(Predicate&& pred)
  {
    auto pos = std::remove_if(mLiterals.begin(), mLiterals.end(), pred);
    long numRemoved = std::distance(pos, mLiterals.end());
    mLiterals.erase(pos, mLiterals.end());

    return numRemoved;
  }

  // Activity heuristics
  void decayActivity(double factor) {
    mActivity *= factor;
  }

  void bumpActivity(double factor) {
    mActivity += factor;
  }

  double activity() const {
    return mActivity;
  }

  void lock() {
    mIsLocked = true;
  }

  void unlock() {
    mIsLocked = false;
  }

  bool isLocked() const {
    return mIsLocked;
  }

private:
  std::vector<Literal> mLiterals;
  bool mIsLearned;
  double mActivity = 1;
  bool mIsLocked = false;
};


class ClauseAllocator
{
  struct Slab
  {
    void* start;
    char* current;
    char* end;
  };

  static constexpr size_t SlabSize = 4096;

public:
  ClauseAllocator()
  {
    this->startNewSlab();
  }

  ClauseAllocator(const ClauseAllocator&) = delete;
  ClauseAllocator& operator=(const ClauseAllocator&) = delete;

  void* allocate(size_t size, size_t alignment)
  {
    size_t padding = calculatePadding(slab().current, alignment);

    if (slab().current + size + padding > slab().end) {
      // If the requested size would overrun this slab, start a new one.
      this->startNewSlab();
    }

    auto alignedPtr = slab().current + padding;
    slab().current = alignedPtr + size;

    return alignedPtr;
  }

  static size_t calculatePadding(void* base, size_t alignment)
  {

  }

private:
  void startNewSlab()
  {
    if (mSlabs.empty() || mCurrentSlab == mSlabs.size() - 1) {
      void* newSlab = ::operator new(SlabSize);
      mSlabs.emplace_back(newSlab, (char*) newSlab, (char*) newSlab + SlabSize);
      mCurrentSlab = mSlabs.size() - 1;
    } else {
      // There is an already allocated slab, we just need to change mCurrentSlab.
      mCurrentSlab++;
    }
  }

  Slab& slab()
  {
    return mSlabs[mCurrentSlab];
  }

private:
  std::vector<Slab> mSlabs;
  size_t mCurrentSlab = 0;
};

class ClauseDatabase
{
public:

  class Iterator
  {
  public:

    Clause& operator*() const
    {
      return mInnerIterator.operator*();
    }

    Clause* operator->()
    {
      return mInnerIterator.operator->();
    }

    Iterator& operator++()
    {
      if (mInnerIterator == mProblemEnd) {
        mInnerIterator = mLearnedBegin;
      } else {
        ++mInnerIterator;
      }
      return *this;
    }

    Iterator operator++(int)
    {
      Iterator tmp = *this;
      ++(*this);
      return tmp;
    }

  private:
    std::vector<Clause>::iterator mInnerIterator;
    std::vector<Clause>::iterator mProblemEnd;
    std::vector<Clause>::iterator mLearnedBegin;
    std::vector<Clause>::iterator mLearnedEnd;
  };

private:
  std::vector<Clause> mProblemClauses;
  std::vector<Clause> mLearnedClauses;
};

} // namespace ivasat

#endif //IVA_SAT_CLAUSE_H
