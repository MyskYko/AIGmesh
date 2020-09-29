#include <iostream>

#include "aig.hpp"

int main(int argc, char **argv) {
  /*
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
  */
  
  extern void interconnectmesh(aigman * p, int N, int T, int W, int fVerbose);
  if(argc < 4) {
    std::cout << "usage aigname meshsize time width" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  int meshsize = atoi(argv[2]);
  int time = atoi(argv[3]);
  int width = atoi(argv[4]);
  aigman p;
  p.read(aigname);


  interconnectmesh(&p, meshsize, time, width, 1);
  
  return 0;
}
