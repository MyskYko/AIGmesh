#include <iostream>

#include "aig.hpp"

int main(int argc, char **argv) {
  extern void Bmc_MeshTest2( aigman * p, int X, int Y, int T, int fVerbose );

  if(argc < 2) {
    std::cout << "specify aigname" << std::endl;
  }
  std::string aigname = argv[1];
  aigman p;
  p.read(aigname);

  Bmc_MeshTest2(&p, 10, 10, 10, 1);
  
  return 0;
}
