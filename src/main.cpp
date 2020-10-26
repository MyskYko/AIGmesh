#include <iostream>

#include "aig.hpp"

int main(int argc, char **argv) {
  extern void hiemesh(aigman * p, std::string resultname, int fVerbose);
  if(argc < 2) {
    std::cout << "usage aigname" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  std::string resname = aigname + ".map.txt";
  aigman p;
  p.read(aigname);
  
  hiemesh(&p, resname, 1);

  return 0;
}
