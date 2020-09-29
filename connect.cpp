#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>

#include <simp/SimpSolver.h>

#include "aig.hpp"

void seqaddertree(Glucose::SimpSolver * pSat, std::vector<int> const &vVars, int k) {
  int v;
  if((int)vVars.size() <= k) {
    return;
  }
  std::vector<int> vCounts;
  Glucose::vec<Glucose::Lit> pLits;
  // first level
  vCounts.push_back(vVars[0]);
  v = pSat->newVar();
  pLits.clear();
  pLits.push(Glucose::mkLit(v, 1));
  pSat->addClause(pLits);
  for(int i = 1; i < k; i++) {
    vCounts.push_back(v);
  }
  // subsequent levels
  for(int j = 1; j < (int)vVars.size(); j++) {
    int x = vVars[j];
    // prohibit overflow (sum>k)
    pLits.clear();
    pLits.push(Glucose::mkLit(vCounts[k-1], 1));
    pLits.push(Glucose::mkLit(x, 1));
    pSat->addClause(pLits);
    if(j == (int)vVars.size()-1) {
      break;
    }
    for(int i = k-1; i > 0; i--) {
      // compute AND of x and i-1 of previous level
      v = pSat->newVar();
      int a = v;
      pLits.clear();
      pLits.push(Glucose::mkLit(a, 1));
      pLits.push(Glucose::mkLit(x));
      pSat->addClause(pLits);
      pLits.clear();
      pLits.push(Glucose::mkLit(a, 1));
      pLits.push(Glucose::mkLit(vCounts[i-1]));
      pSat->addClause(pLits);
      pLits.clear();
      pLits.push(Glucose::mkLit(a));
      pLits.push(Glucose::mkLit(x, 1));
      pLits.push(Glucose::mkLit(vCounts[i-1], 1));
      pSat->addClause(pLits);
      // compute OR of it and i of previous level
      v = pSat->newVar();
      pLits.clear();
      pLits.push(Glucose::mkLit(a, 1));
      pLits.push(Glucose::mkLit(v));
      pSat->addClause(pLits);
      pLits.clear();
      pLits.push(Glucose::mkLit(vCounts[i], 1));
      pLits.push(Glucose::mkLit(v));
      pSat->addClause(pLits);
      pLits.clear();
      pLits.push(Glucose::mkLit(v, 1));
      pLits.push(Glucose::mkLit(a));
      pLits.push(Glucose::mkLit(vCounts[i]));
      pSat->addClause(pLits);
      // keep it at l of this level
      vCounts[i] = v;
    }
    // compute OR of x and 0 of previous level
    v = pSat->newVar();
    pLits.clear();
    pLits.push(Glucose::mkLit(x, 1));
    pLits.push(Glucose::mkLit(v));
    pSat->addClause(pLits);
    pLits.clear();
    pLits.push(Glucose::mkLit(vCounts[0], 1));
    pLits.push(Glucose::mkLit(v));
    pSat->addClause(pLits);
    pLits.clear();
    pLits.push(Glucose::mkLit(v, 1));
    pLits.push(Glucose::mkLit(x));
    pLits.push(Glucose::mkLit(vCounts[0]));
    pSat->addClause(pLits);
    // keep it at 0 of this level
    vCounts[0] = v;
  }
}


void interconnectmesh(aigman * p, int N, int T, int W, int fVerbose) {
  extern int bimander(Glucose::SimpSolver * pSat, std::vector<int> const &vVars, int nbim);
  
  Glucose::SimpSolver * pSat = new Glucose::SimpSolver;
  //pSat->setIncrementalMode();
  //pSat->use_elim = 0;

  Glucose::vec<Glucose::Lit> pLits;
    
  int I = p->nPis;
  int O = p->nPos;
  int DATA = I + p->nGates;
  std::vector<int> fO(DATA);
  for(int i = 0; i < O; i++) {
    fO[(p->vPos[i] >> 1) - 1] = 1;
  }

  // variables
  int IO_n = 0;
  int IO_e = IO_n + DATA * N;
  int IO_s = IO_e + DATA * N;
  int IO_w = IO_s + DATA * N;
  int P = IO_w + DATA * N;
  int S = P + DATA * N * N;
  int V = S + DATA * N * N * T;
  int H = V + DATA * N * N * T;
  int nVars = H + DATA * N * N * T;
  while(nVars >= pSat->nVars()) pSat->newVar();

  int nClause = 0;

  // IO
  for(int i = I; i < DATA; i++) {
    if(fO[i]) {
      pLits.clear();
      for(int z = 0; z < 4 * N; z++) {
	pLits.push(Glucose::mkLit(i + z * DATA + IO_n, 0));
      }
      pSat->addClause(pLits);
      nClause++;
    } else {
      for(int z = 0; z < 4 * N; z++) {
	pSat->addClause(Glucose::mkLit(i + z * DATA + IO_n, 1));
	nClause++;
      }
    }
  }
  for(int i = I; i < DATA; i++) {
    if(!fO[i]) continue;
    // north
    for(int x = 0; x < N; x++) {
      pLits.clear();
      pLits.push(Glucose::mkLit(i + x * DATA + IO_n, 1));
      pLits.push(Glucose::mkLit(i + x * DATA + (N - 1) * DATA * N + (T - 1) * DATA * N * N + S, 0));
      pSat->addClause(pLits);
      nClause++;
    }
    // east
    for(int y = 0; y < N; y++) {
      pLits.clear();
      pLits.push(Glucose::mkLit(i + y * DATA + IO_e, 1));
      pLits.push(Glucose::mkLit(i + (N - 1) * DATA + y * DATA * N + (T - 1) * DATA * N * N + S, 0));
      pSat->addClause(pLits);
      nClause++;
    }
    // south
    for(int x = 0; x < N; x++) {
      pLits.clear();
      pLits.push(Glucose::mkLit(i + x * DATA + IO_s, 1));
      pLits.push(Glucose::mkLit(i + x * DATA + (T - 1) * DATA * N * N + V, 0));
      pSat->addClause(pLits);
      nClause++;
    }
    // west
    for(int y = 0; y < N; y++) {
      pLits.clear();
      pLits.push(Glucose::mkLit(i + y * DATA + IO_w, 1));
      pLits.push(Glucose::mkLit(i + y * DATA * N + (T - 1) * DATA * N * N + H, 0));
      pSat->addClause(pLits);
      nClause++;
    }
  }

  // PE
  for(int y = 0; y < N; y++) {
    for(int x = 0; x < N; x++) {
      for(int i = 0; i < I; i++) {
	pSat->addClause(Glucose::mkLit(i + x * DATA + y * DATA * N + P, 1));
	nClause++;
      }
      for(int i = I; i < DATA; i++) {
	for(int fi = 0; fi < 2; fi++) {
	  int j = (p->vObjs[i + i + 2 + fi] >> 1) - 1;
	  pLits.clear();
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + P, 1));
	  pLits.push(Glucose::mkLit(j + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + H, 0));
	  pSat->addClause(pLits);
	  nClause++;
	}
      }
    }
  }

  // Switch
  for(int y = 0; y < N; y++) {
    for(int x = 0; x < N; x++) {
      // first cycle
      for(int i = 0; i < DATA; i++) {
	pLits.clear();
	pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + S, 1));
	if(x + 1 == N && i < I) {
	  pLits.push(Glucose::mkLit(i + y * DATA + IO_e, 0));
	}
	if(y + 1 == N && i < I) {
	  pLits.push(Glucose::mkLit(i + x * DATA + IO_n, 0));
	}
	pSat->addClause(pLits);
	nClause++;
      }
      // the other cycles
      for(int k = 1; k < T; k++) {
	for(int i = 0; i < DATA; i++) {
	  pLits.clear();
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + k * DATA * N * N + S, 1));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k - 1) * DATA * N * N + S, 0));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k - 1) * DATA * N * N + H, 0));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k - 1) * DATA * N * N + V, 0));
	  if(x + 1 < N) {
	    pLits.push(Glucose::mkLit(i + (x + 1) * DATA + y * DATA * N + (k - 1) * DATA * N * N + H, 0));
	  } else if(i < I) {
	    pLits.push(Glucose::mkLit(i + y * DATA + IO_e, 0));
	  }
	  if(y + 1 < N) {
	    pLits.push(Glucose::mkLit(i + x * DATA + (y + 1) * DATA * N + (k - 1) * DATA * N * N + V, 0));
	  } else if(i < I) {
	    pLits.push(Glucose::mkLit(i + x * DATA + IO_n, 0));
	  }
	  pSat->addClause(pLits);
	  nClause++;
	}
      }
      // prop
      for(int k = 0; k < T - 1; k++) {
	for(int i = 0; i < DATA; i++) {
	  pLits.clear();
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + k * DATA * N * N + S, 1));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k + 1) * DATA * N * N + S, 0));
	  pSat->addClause(pLits);
	  nClause++;
	}
      }
    }
  }

  // Vertical
  for(int y = 0; y < N; y++) {
    for(int x = 0; x < N; x++) {
      // first cycle
      for(int i = 0; i < DATA; i++) {
	pLits.clear();
	pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + V, 1));
	pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + P, 0));
	if(y == 0 && i < I) {
	  pLits.push(Glucose::mkLit(i + x * DATA + IO_s, 0));
	}
	pSat->addClause(pLits);
	nClause++;
      }
      // the other cycles
      for(int k = 1; k < T; k++) {
	for(int i = 0; i < DATA; i++) {
	  pLits.clear();
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + k * DATA * N * N + V, 1));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + P, 0));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k - 1) * DATA * N * N + V, 0));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k - 1) * DATA * N * N + S, 0));
	  if(y > 0) {
	    pLits.push(Glucose::mkLit(i + x * DATA + (y - 1) * DATA * N + (k - 1) * DATA * N * N + S, 0));
	  } else if(i < I) {
	    pLits.push(Glucose::mkLit(i + x * DATA + IO_s, 0));
	  }
	  pSat->addClause(pLits);
	  nClause++;
	}
      }
      // prop
      for(int k = 0; k < T - 1; k++) {
	for(int i = 0; i < DATA; i++) {
	  pLits.clear();
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + k * DATA * N * N + V, 1));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k + 1) * DATA * N * N + V, 0));
	  pSat->addClause(pLits);
	  nClause++;
	}
      }
    }
  }
  
  // Horizontal
  for(int y = 0; y < N; y++) {
    for(int x = 0; x < N; x++) {
      // first cycle
      for(int i = 0; i < DATA; i++) {
	pLits.clear();
	pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + H, 1));
	if(x == 0 && i < I) {
	  pLits.push(Glucose::mkLit(i + y * DATA + IO_w, 0));
	}
	pSat->addClause(pLits);
	nClause++;
      }
      // the other cycles
      for(int k = 1; k < T; k++) {
	for(int i = 0; i < DATA; i++) {
	  pLits.clear();
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + k * DATA * N * N + H, 1));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k - 1) * DATA * N * N + H, 0));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k - 1) * DATA * N * N + S, 0));
	  if(x > 0) {
	    pLits.push(Glucose::mkLit(i + (x - 1) * DATA + y * DATA * N + (k - 1) * DATA * N * N + S, 0));
	  } else if(i < I) {
	    pLits.push(Glucose::mkLit(i + y * DATA + IO_w, 0));
	  }
	  pSat->addClause(pLits);
	  nClause++;
	}
      }
      // prop
      for(int k = 0; k < T - 1; k++) {
	for(int i = 0; i < DATA; i++) {
	  pLits.clear();
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + k * DATA * N * N + H, 1));
	  pLits.push(Glucose::mkLit(i + x * DATA + y * DATA * N + (k + 1) * DATA * N * N + H, 0));
	  pSat->addClause(pLits);
	  nClause++;
	}
      }
    }
  }

  // AM(W) for IO
  if(W > 0) {
    for(int z = 0; z < 4 * N; z++) {
      std::vector<int> vVars;
      for(int i = 0; i < DATA; i++) {
	vVars.push_back(i + z * DATA + IO_n);
      }
      seqaddertree(pSat, vVars, W);
    }
  }
  
  // AM(1) for PE
  for(int y = 0; y < N; y++) {
    for(int x = 0; x < N; x++) {
      std::vector<int> vVars;
      for(int i = 0; i < DATA; i++) {
	vVars.push_back(i + x * DATA + y * DATA * N + P);
      }
      bimander(pSat, vVars, 2);
    }
  }

  // AM(2W) for Switch
  if(W > 0) {
    for(int y = 0; y < N; y++) {
      for(int x = 0; x < N; x++) {
	std::vector<int> vVars;
	for(int i = 0; i < DATA; i++) {
	  vVars.push_back(i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + S);
	}
	seqaddertree(pSat, vVars, W + W);
      }
    }
  }

  // AM(W) for Vertical
  if(W > 0) {
    for(int y = 0; y < N; y++) {
      for(int x = 0; x < N; x++) {
	std::vector<int> vVars;
	for(int i = 0; i < DATA; i++) {
	  vVars.push_back(i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + V);
	}
	seqaddertree(pSat, vVars, W);
      }
    }
  }

  // AM(W) for Horizontal
  if(W > 0) {
    for(int y = 0; y < N; y++) {
      for(int x = 0; x < N; x++) {
	std::vector<int> vVars;
	for(int i = 0; i < DATA; i++) {
	  vVars.push_back(i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + H);
	}
	seqaddertree(pSat, vVars, W);
      }
    }
  }

  // solve
  printf("nVars %d, nClauses %d\n", pSat->nVars(), pSat->nClauses());
  auto start = std::chrono::system_clock::now();
  int status = pSat->solve();
  auto end = std::chrono::system_clock::now();
  std::cout << "time : " << std::chrono::duration_cast<std::chrono::milliseconds>(end-start).count() / 1000. << " s" << std::endl;
  if(status == 0) {
    printf("UNSAT\n");
  } else {
    printf("SAT\n");

    /*
    for(int z = 0; z < 4 * N; z++) {
      printf("%d:", z);
      for(int i = 0; i < DATA; i++) {
	if(pSat->model[i + z * DATA + IO_n] == l_True) {
	  printf("%d ", i);
	}
      }
      printf("\n");
    }

    for(int y = 0; y < N; y++) {
      for(int x = 0; x < N; x++) {
	printf("%d %d:\n", x, y);
	for(int i = 0; i < DATA; i++) {
	  if(pSat->model[i + x * DATA + y * DATA * N + P] == l_True) {
	    printf("\tP %d\n", i);
	  }
	  if(pSat->model[i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + S] == l_True) {
	    printf("\tS %d\n", i);
	  }
	  if(pSat->model[i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + V] == l_True) {
	    printf("\tV %d\n", i);
	  }
	  if(pSat->model[i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + H] == l_True) {
	    printf("\tH %d\n", i);
	  }
	}
      }
    }
    */

    int fcolor = 1;
    int ww = 3; // log10(DATA-1) + 2
    int bw = ww + ww + 2;
    int bh = W > 0? W + 2: 5;
    std::vector<std::string> m(1000); // top-side down map
    // south
    for(int l = 0; l < bh; l++) {
      m[l] += std::string(bw, ' ');
    }
    for(int x = 0; x < N; x++) {
      for(int l = 0; l < bh; l++) {
	m[l] += std::string(bw, ' ');
      }
      std::vector<int> v;
      for(int i = 0; i < DATA; i++) {
	if(pSat->model[i + x * DATA + IO_s] == l_True) {
	  v.push_back(i);
	}
      }
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[l] += "\x1b[35m";
	}
      }
      m[0] += std::string(bw, '#');
      int vi = 0;
      for(int l = 1; l < bh - 1; l++) {
	m[l] += "#";
	for(int two = 0; two < 2; two++) {
	  std::string s = "";
	  if(vi < v.size()) {
	    s = std::to_string(v[vi++]);
	  }
	  s = std::string(ww - s.size(), ' ') + s;
	  m[l] += s;
	}
	m[l] += "#";
      }
      m[bh - 1] += std::string(bw, '#');
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[l] += "\x1b[m";
	}
      }
    }
    // west
    for(int y = 0; y < N; y++) {
      for(int l = 0; l < bh; l++) {
	m[(2 * y + 1) * bh + l] += std::string(bw, ' ');
      }
      std::vector<int> v;
      for(int i = 0; i < DATA; i++) {
	if(pSat->model[i + y * DATA + IO_w] == l_True) {
	  v.push_back(i);
	}
      }
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[(2 * y + 2) * bh + l] += "\x1b[35m";
	}
      }
      m[(2 * y + 2) * bh] += std::string(bw, '#');
      int vi = 0;
      for(int l = 1; l < bh - 1; l++) {
	m[(2 * y + 2) * bh + l] += "#";
	for(int two = 0; two < 2; two++) {
	  std::string s = "";
	  if(vi < v.size()) {
	    s = std::to_string(v[vi++]);
	  }
	  s = std::string(ww - s.size(), ' ') + s;
	  m[(2 * y + 2) * bh + l] += s;
	}
	m[(2 * y + 2) * bh + l] += "#";
      }
      m[(2 * y + 2) * bh + bh - 1] += std::string(bw, '#');
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[(2 * y + 2) * bh + l] += "\x1b[m";
	}
      }
    }
    // north
    for(int l = 0; l < bh; l++) {
      m[(2 * N + 1) * bh + l] += std::string(bw, ' ');
    }
    for(int x = 0; x < N; x++) {
      for(int l = 0; l < bh; l++) {
	m[(2 * N + 1) * bh + l] += std::string(bw, ' ');
      }
      std::vector<int> v;
      for(int i = 0; i < DATA; i++) {
	if(pSat->model[i + x * DATA + IO_n] == l_True) {
	  v.push_back(i);
	}
      }
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[(2 * N + 1) * bh + l] += "\x1b[35m";
	}
      }
      m[(2 * N + 1) * bh] += std::string(bw, '#');
      int vi = 0;
      for(int l = 1; l < bh - 1; l++) {
	m[(2 * N + 1) * bh + l] += "#";
	for(int two = 0; two < 2; two++) {
	  std::string s = "";
	  if(vi < v.size()) {
	    s = std::to_string(v[vi++]);
	  }
	  s = std::string(ww - s.size(), ' ') + s;
	  m[(2 * N + 1) * bh + l] += s;
	}
	m[(2 * N + 1) * bh + l] += "#";
      }
      m[(2 * N + 1) * bh + bh - 1] += std::string(bw, '#');
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[(2 * N + 1) * bh + l] += "\x1b[m";
	}
      }
    }
    // mesh
    for(int x = 0; x < N; x++) {
      for(int y = 0; y < N; y++) {
	for(int t = 0; t < 4; t++) { 
	  // t=0 PE, t=1 H, t=2 V, t=3 S
	  std::vector<int> v;
	  for(int i = 0; i < DATA; i++) {
	    if(t == 0 && pSat->model[i + x * DATA + y * DATA * N + P] == l_True) {
	      v.push_back(i);
	    }
	    if(t == 3 && pSat->model[i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + S] == l_True) {
	      v.push_back(i);
	    }
	    if(t == 2 && pSat->model[i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + V] == l_True) {
	      v.push_back(i);
	    }
	    if(t == 1 && pSat->model[i + x * DATA + y * DATA * N + (T - 1) * DATA * N * N + H] == l_True) {
	      v.push_back(i);
	    }
	  }
	  if(fcolor && t == 0) {
	    for(int l = 0; l < bh; l++) {
	      m[(2 * y + t % 2 + 1) * bh + l] += "\x1b[33m";
	    }
	  }
	  m[(2 * y + t % 2 + 1) * bh] += std::string(bw, '#');
	  int vi = 0;
	  for(int l = 1; l < bh - 1; l++) {
	    m[(2 * y + t % 2 + 1) * bh + l] += "#";
	    for(int two = 0; two < 2; two++) {
	      std::string s = "";
	      if(vi < v.size()) {
		s = std::to_string(v[vi++]);
	      }
	      s = std::string(ww - s.size(), ' ') + s;
	      m[(2 * y + t % 2 + 1) * bh + l] += s;
	    }
	    m[(2 * y + t % 2 + 1) * bh + l] += "#";
	  }
	  m[(2 * y + t % 2 + 1) * bh + bh - 1] += std::string(bw, '#');
	  if(fcolor && t == 0) {
	    for(int l = 0; l < bh; l++) {
	      m[(2 * y + t % 2 + 1) * bh + l] += "\x1b[m";
	    }
	  }
	}
      }
    }
    // east
    for(int y = 0; y < N; y++) {
      std::vector<int> v;
      for(int i = 0; i < DATA; i++) {
	if(pSat->model[i + y * DATA + IO_e] == l_True) {
	  v.push_back(i);
	}
      }
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[(2 * y + 2) * bh + l] += "\x1b[35m";
	}
      }
      m[(2 * y + 2) * bh] += std::string(bw, '#');
      int vi = 0;
      for(int l = 1; l < bh - 1; l++) {
	m[(2 * y + 2) * bh + l] += "#";
	for(int two = 0; two < 2; two++) {
	  std::string s = "";
	  if(vi < v.size()) {
	    s = std::to_string(v[vi++]);
	  }
	  s = std::string(ww - s.size(), ' ') + s;
	  m[(2 * y + 2) * bh + l] += s;
	}
	m[(2 * y + 2) * bh + l] += "#";
      }
      m[(2 * y + 2) * bh + bh - 1] += std::string(bw, '#');
      if(fcolor) {
	for(int l = 0; l < bh; l++) {
	  m[(2 * y + 2) * bh + l] += "\x1b[m";
	}
      }
    }

    for(int l = (2 * N + 1) * bh + bh - 1; l >= 0; l--) {
      std::cout << m[l] << std::endl;
    }

    for(int i = I; i < DATA; i++) {
      int j0 = (p->vObjs[i + i + 2] >> 1) - 1;
      int j1 = (p->vObjs[i + i + 3] >> 1) - 1;
      printf("%d = %d * %d\n", i, j0, j1);
    }    
  }
  
  delete pSat;  
}
