#ifndef IVA_SAT_ALLOCATOR_H
#define IVA_SAT_ALLOCATOR_H

namespace ivasat
{

class StackAllocator
{
  struct Slab
  {
    void* start;
    char* current;
    char* end;
  };

  static constexpr size_t SlabSize = 4096;
public:

  StackAllocator()
  {
    this->startNewSlab();
  }

  StackAllocator(const StackAllocator&) = delete;
  StackAllocator& operator=(const StackAllocator&) = delete;

  void* allocate(size_t size, size_t alignment)
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

}

#endif //IVA_SAT_ALLOCATOR_H
