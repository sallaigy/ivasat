#include "ivasat/ivasat.h"

#include <istream>
#include <cassert>

using namespace ivasat;

namespace
{

class DimacsStream
{
public:
  explicit DimacsStream(std::istream& stream)
    : mStream(stream)
  {}

  std::unique_ptr<Instance> parse();

  void skipLine();
  std::string nextToken();

private:
  std::istream& mStream;
};

} // namespace

std::unique_ptr<Instance> ivasat::parseDimacs(std::istream& input)
{
  return DimacsStream{input}.parse();
}

std::unique_ptr<Instance> DimacsStream::parse()
{
  // Parse file header
  size_t numVars = 0;
  size_t numClauses = 0;

  while (mStream) {
    int curr = mStream.get();
    if (curr == 'c') {
      skipLine();
    } else if (curr == 'p') {
      std::string cnfToken = nextToken();
      assert(cnfToken == "cnf");

      numVars = std::stoi(nextToken());
      numClauses = std::stoi(nextToken());
      break;
    }
  }

  // TODO: mStream.eof()
  std::vector<std::vector<int>> clauses(numClauses, std::vector<int>{});
  for (size_t i = 0; i < numClauses; ++i) {
    std::string token = nextToken();
    while (token != "0") {
      int value = std::stoi(token);
      clauses[i].push_back(value);
      token = nextToken();
    }
  }

  return std::make_unique<Instance>(numVars, clauses);
}

std::string DimacsStream::nextToken()
{
  // Skip all whitespace
  int curr = mStream.get();
  while (isspace(curr)) {
    curr = mStream.get();
  }

  std::string buffer;
  while (isalnum(curr) || curr == '-') {
    buffer += static_cast<char>(curr);
    curr = mStream.get();
  }

  return buffer;
}

void DimacsStream::skipLine()
{
  int curr = mStream.get();
  while (mStream && curr != '\n') {
    curr = mStream.get();
  }
}

