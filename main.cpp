#include <iostream>

#include "aig.hpp"

int main(int argc, char **argv) {
  extern void Bmc_MeshTest( aigman * p, int X, int Y, int T, int fVerbose, bool inputbuf );
  extern void Bmc_MeshTest2( aigman * p, int X, int Y, int T, int fVerbose );

  if(argc < 4) {
    std::cout << "usage aigname meshsize cycle" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  int meshsize = atoi(argv[2]);
  int cycle = atoi(argv[3]);
  aigman p;
  p.read(aigname);

  Bmc_MeshTest(&p, meshsize, meshsize, cycle, 1, 1);
  
  return 0;
}
