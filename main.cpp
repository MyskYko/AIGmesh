#include <iostream>

#include "aig.hpp"

int main(int argc, char **argv) {
  extern void Bmc_MeshTest( aigman * p, int X, int Y, int T, int fVerbose, bool inputbuf, bool iteAMO );
  extern void Bmc_MeshTest2( aigman * p, int X, int Y, int T, int fVerbose );

  if(argc < 5) {
    std::cout << "usage aigname meshsize cycle iterate" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  int meshsize = atoi(argv[2]);
  int cycle = atoi(argv[3]);
  int iteAMO = atoi(argv[4]);
  aigman p;
  p.read(aigname);

  Bmc_MeshTest(&p, meshsize, meshsize, cycle, 1, 1, iteAMO);
  
  return 0;
}
