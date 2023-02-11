#include "ivasat/ivasat.h"

#include <iostream>
#include <fstream>

int main(int argc, char* argv[])
{
  if (argc != 2) {
    std::cerr << "USAGE: ivasat <file>\n";
    return 1;
  }

  std::string file = argv[1];
  std::ifstream input(file);

  auto instance = ivasat::parseDimacs(input);

  auto status = instance->check();

  std::cout << status << "\n";
}
