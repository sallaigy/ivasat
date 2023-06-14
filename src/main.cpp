#include "ivasat/ivasat.h"
#include "Solver.h"

#include <iostream>
#include <fstream>
#include <csignal>

static std::unique_ptr<ivasat::Solver> solver;

static void interrupt_solver([[maybe_unused]] int num)
{
  solver->dumpStats(std::cout);
  exit(1);
}

int main(int argc, char* argv[])
{
  if (argc != 2) {
    std::cerr << "USAGE: ivasat <file>\n";
    return 1;
  }

  std::string file = argv[1];
  std::ifstream input(file);

  auto instance = ivasat::parseDimacs(input);
  solver = std::make_unique<ivasat::Solver>(*instance);

  signal(SIGINT, interrupt_solver);

  auto status = solver->check();
  solver->dumpStats(std::cout);

  std::cout << status << "\n";
}
