#include <iostream>
#include <map>
#include <vector>
#include <string>
#include <queue>
#include <algorithm>
#include <chrono>

#include "solver.hpp"

#include "aig.hpp"
#include "global.hpp"

class hienode {
public:
  aigman * aig;
  std::vector<int> inputs; // nodes at parental H and inputted to gates but not outputted by gates
  std::vector<int> gates;
  std::vector<int> outputs; // nodes at parental V and outputted by gates

  int level; // ceil(log4(total gates)) - 1
  int blocksize; // = 4^level
  int width; // = 4^(level+1)

  std::vector<std::vector<std::vector<int> > > P;
  std::vector<std::vector<std::vector<int> > > V;
  std::vector<std::vector<std::vector<int> > > H;
  std::vector<std::vector<std::vector<int> > > S;
  
  std::vector<std::vector<hienode *> > children;

  void eval();

  ~hienode() {
    if(!children.empty()) {
      delete children[0][0];
      delete children[0][1];
      delete children[1][0];
      delete children[1][1];
    }
  }
};

void hienode::eval() {
  //gurobi * pSat = new gurobi;
  glucose * pSat = new glucose;

  std::vector<int> vLits;

  int nInputs = inputs.size();
  int nOutputs = outputs.size();
  int nData = 0;
  std::map<int, int> m;
  std::map<int, int> mr;
  for(int input: inputs) {
    mr[nData] = input;
    m[input] = nData++;
  }
  for(int gate: gates) {
    mr[nData] = gate;
    m[gate] = nData++;
  }

  int nLength = 2;
  int nBlock = nLength * nLength;
  int nDelay = 5; // is 5 enough? I think 7 is max, from right bottom to left top

  // zero
  pSat->newvar();
  pSat->addclause(-1);
    
  // variables
  int headI = 2;
  int headO = headI + nInputs * nLength;
  int headP = headO + nOutputs * nLength;
  int headV = headP + nData * nBlock;
  int headH = headV + nData * nBlock * nDelay;
  int headS = headH + nData * nBlock * nDelay;
  int nVars = headS + nData * nBlock * nDelay;
  while(nVars - 1> pSat->nVars) pSat->newvar();

  // Processor (2-LUT)
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      for(int i = 0; i < nInputs; i++) {
	pSat->addclause(-(i + x * nData + y * nData * nLength + headP));
      }
      for(int i = nInputs; i < nData; i++) {
	int gate = mr[i];
	for(int fi = 0; fi < 2; fi++) {
	  int input = aig->vObjs[gate + gate + fi] >> 1;
	  int j = m[input];
	  vLits.clear();
	  vLits.push_back(-(i + x * nData + y * nData * nLength + headP));
	  vLits.push_back((j + x * nData + y * nData * nLength + headP));
	  vLits.push_back((j + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headH));
	  pSat->addclause(vLits);
	}
      }
    }
  }

  // Switch box
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      // first cycle
      for(int i = 0; i < nData; i++) {
	vLits.clear();
	vLits.push_back(-(i + x * nData + y * nData * nLength + headS));
	if(y + 1 == nLength && i < nInputs) {
	  vLits.push_back((i + x * nInputs + headI));
	}
	pSat->addclause(vLits);
      }
      // the other cycles
      for(int k = 1; k < nDelay; k++) {
	for(int i = 0; i < nData; i++) {
	  vLits.clear();
	  vLits.push_back(-(i + x * nData + y * nData * nLength + k * nData * nBlock + headS));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k - 1) * nData * nBlock + headS));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k - 1) * nData * nBlock + headH));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k - 1) * nData * nBlock + headV));
	  if(x + 1 < nLength) {
	    vLits.push_back((i + (x + 1) * nData + y * nData * nLength + (k - 1) * nData * nBlock + headH));
	  }
	  if(y + 1 < nLength) {
	    vLits.push_back((i + x * nData + (y + 1) * nData * nLength + (k - 1) * nData * nBlock + headV));
	  }
	  pSat->addclause(vLits);
	}
      }
      // prop
      for(int k = 0; k < nDelay - 1; k++) {
	for(int i = 0; i < nData; i++) {
	  vLits.clear();
	  vLits.push_back(-(i + x * nData + y * nData * nLength + k * nData * nBlock + headS));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k + 1) * nData * nBlock + headS));
	  pSat->addclause(vLits);
	}
      }
    }
  }

  // Vertical line
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      // first cycle
      for(int i = 0; i < nData; i++) {
	vLits.clear();
	vLits.push_back(-(i + x * nData + y * nData * nLength + headV));
	vLits.push_back((i + x * nData + y * nData * nLength + headP));
	pSat->addclause(vLits);
      }
      // the other cycles
      for(int k = 1; k < nDelay; k++) {
	for(int i = 0; i < nData; i++) {
	  vLits.clear();
	  vLits.push_back(-(i + x * nData + y * nData * nLength + k * nData * nBlock + headV));
	  vLits.push_back((i + x * nData + y * nData * nLength + headP));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k - 1) * nData * nBlock + headV));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k - 1) * nData * nBlock + headS));
	  if(y > 0) {
	    vLits.push_back((i + x * nData + (y - 1) * nData * nLength + (k - 1) * nData * nBlock + headS));
	  }
	  pSat->addclause(vLits);
	}
      }
      // prop
      for(int k = 0; k < nDelay - 1; k++) {
	for(int i = 0; i < nData; i++) {
	  vLits.clear();
	  vLits.push_back(-(i + x * nData + y * nData * nLength + k * nData * nBlock + headV));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k + 1) * nData * nBlock + headV));
	  pSat->addclause(vLits);
	}
      }
    }
  }
  
  // Horizontal line
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      // first cycle
      for(int i = 0; i < nData; i++) {
	pSat->addclause(-(i + x * nData + y * nData * nLength + headH));
      }
      // the other cycles
      for(int k = 1; k < nDelay; k++) {
	for(int i = 0; i < nData; i++) {
	  vLits.clear();
	  vLits.push_back(-(i + x * nData + y * nData * nLength + k * nData * nBlock + headH));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k - 1) * nData * nBlock + headH));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k - 1) * nData * nBlock + headS));
	  if(x > 0) {
	    vLits.push_back((i + (x - 1) * nData + y * nData * nLength + (k - 1) * nData * nBlock + headS));
	  }
	  pSat->addclause(vLits);
	}
      }
      // prop
      for(int k = 0; k < nDelay - 1; k++) {
	for(int i = 0; i < nData; i++) {
	  vLits.clear();
	  vLits.push_back(-(i + x * nData + y * nData * nLength + k * nData * nBlock + headH));
	  vLits.push_back((i + x * nData + y * nData * nLength + (k + 1) * nData * nBlock + headH));
	  pSat->addclause(vLits);
	}
      }
    }
  }

  // Outputs
  for(int y = 0; y < nLength; y++) {
    int x = nLength - 1;
    for(int i = 0; i < nOutputs; i++) {
      int output = outputs[i];
      int j = m[output];
      vLits.clear();
      vLits.push_back(-(i + y * nOutputs + headO));
      vLits.push_back((j + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headS));
      pSat->addclause(vLits);
    }
  }
  for(int i = 0; i < nOutputs; i++) {
    vLits.clear();
    for(int y = 0; y < nLength; y++) {
      vLits.push_back((i + y * nOutputs + headO));
    }
    pSat->addclause(vLits);
  }

  // AMK for Inputs
  for(int x = 0; x < nLength; x++) {
    vLits.clear();
    for(int i = 0; i < nInputs; i++) {
      vLits.push_back(i + x * nInputs + headI);
    }
    pSat->amk(vLits, width);
  }
  
  // AMK for Processor
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      vLits.clear();
      for(int i = 0; i < nData; i++) {
	vLits.push_back(i + x * nData + y * nData * nLength + headP);
      }
      pSat->amk(vLits, blocksize);
    }
  }

  // AMK for Switch box
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      vLits.clear();
      for(int i = 0; i < nData; i++) {
	vLits.push_back(i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headS);
      }
      pSat->amk(vLits, width + width);
    }
  }

  // AMK for Vertical line
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      vLits.clear();
      for(int i = 0; i < nData; i++) {
	vLits.push_back(i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headV);
      }
      pSat->amk(vLits, width);
    }
  }
  
  // AMK for Horizontal line
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      vLits.clear();
      for(int i = 0; i < nData; i++) {
	vLits.push_back(i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headH);
      }
      pSat->amk(vLits, width);
    }
  }

  // AMK for Outputs
  for(int y = 0; y < nLength; y++) {
    vLits.clear();
    for(int i = 0; i < nOutputs; i++) {
      vLits.push_back(i + y * nOutputs + headO);
    }
    pSat->amk(vLits, width);
  }

  /*
  {
    pSat->objective = "minimize \n";
    for(int y = 0; y < nLength; y++) {
      for(int x = 0; x < nLength; x++) {
	for(int i = 0; i < nData; i++) {
	  pSat->objective += "x" + std::to_string(i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headV) + " + ";
	}
      }
    }
    for(int y = 0; y < nLength; y++) {
      for(int x = 0; x < nLength; x++) {
	for(int i = 0; i < nData; i++) {
	  pSat->objective += "x" + std::to_string(i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headH) + " + ";
	}
      }
    }
    pSat->objective.pop_back();
    pSat->objective.pop_back();
    pSat->objective += "\n";
  }
  */

  // solve
  auto start = std::chrono::system_clock::now();
  bool status = pSat->solve();
  auto end = std::chrono::system_clock::now();
  std::cout << "time : " << std::chrono::duration_cast<std::chrono::milliseconds>(end-start).count() / 1000. << " s" << std::endl;
  if(status == 0) {
    printf("UNSAT\n");
  } else {
    printf("SAT\n");
    for(int x = 0; x < nLength; x++) {
      printf("input %d:", x);
      for(int i = 0; i < nInputs; i++) {
	if(pSat->model[i + x * nInputs + headI]) {
	  printf(" %d", i);
	}
      }
      printf("\n");
    }
    for(int y = 0; y < nLength; y++) {
      printf("output %d:", y);
      for(int i = 0; i < nOutputs; i++) {
	if(pSat->model[i + y * nOutputs + headO]) {
	  printf(" %d", i);
	}
      }
      printf("\n");
    }
    
    for(int y = 0; y < nLength; y++) {
      for(int x = 0; x < nLength; x++) {
	printf("%d %d:\n", x, y);
	printf("\tS");
	for(int i = 0; i < nData; i++) {
	  if(pSat->model[i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headS]) {
	    printf(" %d", i);
	  }
	}
	printf("\n");
	printf("\tH");
	for(int i = 0; i < nData; i++) {
	  if(pSat->model[i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headH]) {
	    printf(" %d", i);
	  }
	}
	printf("\n");
	printf("\tP");
	for(int i = 0; i < nData; i++) {
	  if(pSat->model[i + x * nData + y * nData * nLength + headP]) {
	    printf(" %d", i);
	  }
	}
	printf("\n");
	printf("\tV");
	for(int i = 0; i < nData; i++) {
	  if(pSat->model[i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headV]) {
	    printf(" %d", i);
	  }
	}
	printf("\n");
      }
    }
  }

  P.resize(nLength);
  V.resize(nLength);
  H.resize(nLength);
  S.resize(nLength);
  for(int x = 0; x < nLength; x++) {
    P[x].resize(nLength);
    V[x].resize(nLength);
    H[x].resize(nLength);
    S[x].resize(nLength);
    for(int y = 0; y < nLength; y++) {
      for(int i = 0; i < nData; i++) {
	if(pSat->model[i + x * nData + y * nData * nLength + headP]) {
	  P[x][y].push_back(mr[i]);
	}
      }
      for(int i = 0; i < nData; i++) {
	if(pSat->model[i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headV]) {
	  V[x][y].push_back(mr[i]);
	}
      }
      for(int i = 0; i < nData; i++) {
	if(pSat->model[i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headH]) {
	  H[x][y].push_back(mr[i]);
	}
      }
      for(int i = 0; i < nData; i++) {
	if(pSat->model[i + x * nData + y * nData * nLength + (nDelay - 1) * nData * nBlock + headS]) {
	  S[x][y].push_back(mr[i]);
	}
      }
    }
  }

  delete pSat;
  if(level == 0) return;

  children.resize(2);
  children[0].resize(2);
  children[1].resize(2);
  for(int y = 0; y < nLength; y++) {
    for(int x = 0; x < nLength; x++) {
      hienode * child = new hienode;
      child->aig = aig;
      {
	std::vector<bool> used(aig->nObjs);
	for(int gate: P[x][y]) {
	  for(int fi = 0; fi < 2; fi++) {
	    int input = aig->vObjs[gate + gate + fi] >> 1;
	    used[input] = 1;
	  }
	}
	for(int gate: P[x][y]) {
	  used[gate] = 0;
	}
	for(int input: H[x][y]) {
	  if(used[input]) {
	    child->inputs.push_back(input);
	  }
	}
      }
      child->gates = P[x][y];
      {
	std::vector<bool> used(aig->nObjs);
	for(int gate: P[x][y]) {
	  used[gate] = 1;
	}
	for(int output: V[x][y]) {
	  if(used[output]) {
	    child->outputs.push_back(output);
	  }
	}
      }
      child->level = level - 1;
      child->blocksize = 1 << (2 * child->level);
      child->width = child->blocksize << 2;
      
      child->eval();
      
      children[x][y] = child;
    }
  }
}

void dumpresult(hienode * node, std::ofstream & f) {
  for(int y = 0; y < 2; y++) {
    for(int x = 0; x < 2; x++) {
      for(int i: node->V[x][y]) {
	f << i << " ";
      }
      f << std::endl;
      for(int i: node->H[x][y]) {
	f << i << " ";
      }
      f << std::endl;
      if(node->level == 0) {
	for(int i: node->P[x][y]) {
	  f << i << " ";
	}
	f << std::endl;
      } else {
	dumpresult(node->children[x][y], f);
      }
    }
  }
}

void hiemesh(aigman * aig, std::string resultname, int fVerbose) {
  assert(aig->nLats == 0);
  hienode root;
  root.aig = aig;
  for(int i = 1; i < aig->nPis + 1; i++) {
    root.inputs.push_back(i);
  }
  for(int i = aig->nPis + aig->nLats + 1; i < aig->nObjs; i++) {
    root.gates.push_back(i);
  }
  for(int i: aig->vPos) {
    root.outputs.push_back(i >> 1);
  }
  int l = clog2(aig->nGates);
  root.level = l / 2 + l % 2 - 1;
  root.blocksize = 1 << (2 * root.level);
  root.width = root.blocksize << 2;

  root.eval();

  std::ofstream f(resultname);
  f << root.level << " " << aig->nObjs << std::endl;
  dumpresult(&root, f);

  f.close();
}
