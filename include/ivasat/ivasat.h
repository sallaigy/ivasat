#ifndef IVA_SAT_IVASAT_H
#define IVA_SAT_IVASAT_H

#include <memory>
#include <vector>
#include <iosfwd>


namespace ivasat
{

enum class Status
{
  Sat,
  Unsat,
  Unknown
};

class Instance
{
public:
  Instance(unsigned int numVariables, const std::vector<std::vector<int>>& clauses)
    : mNumVariables(numVariables), mClauses(clauses)
  {}

  Status check();

  /// If \p check was called before and it returned the status \p SAT, this function returns the model associated with
  /// the satisfiable formula.
  std::vector<bool> model() const;

  unsigned numVariables() const
  {
    return mNumVariables;
  }

  const std::vector<std::vector<int>>& clauses() const
  {
    return mClauses;
  }

private:
  unsigned mNumVariables;
  std::vector<std::vector<int>> mClauses;
  std::vector<bool> mModel;
};

std::ostream& operator<<(std::ostream& os, Status status);

std::unique_ptr<Instance> parseDimacs(std::istream& input);

} // namespace ivasat

#endif //IVA_SAT_IVASAT_H
