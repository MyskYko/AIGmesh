#include "solver.hpp"
#include "global.hpp"

void solver::bimander(std::vector<int> const &vLits, int nbim) {
  std::vector<int> vLits2;
  int m = vLits.size() / nbim + vLits.size() % nbim;
  int nb = clog2(m);
  int c = nVars + 1;
  for(int k = 0; k < nb; k++) {
    newvar();
  }
  for(int i = 0; i < m; i++) {
    vLits2.clear();
    for(int j = 0; j < nbim && i*nbim + j < vLits.size(); j++) {
      vLits2.push_back(vLits[i*nbim + j]);
    }
    if(vLits2.size() > 1) {
      // naive
      for(int p = 0; p < vLits2.size(); p++) {
	for( int q = p+1; q < vLits2.size(); q++) {
	  addclause(-vLits2[p], -vLits2[q]);
	}
      }
    }
    for(int k = 0; k < nb; k++) {
      int b = 1 << k;
      if(i & b) {
	for(int j = 0; j < nbim && i*nbim + j < vLits.size(); j++) {
	  addclause(-vLits[i*nbim+j], c + k);
	}
      }
      else {
	for(int j = 0; j < nbim && i*nbim + j < vLits.size(); j++) {
	  addclause(-vLits[i*nbim+j], -(c + k));
	}
      }
    }
  }
}

void solver::comparator(int a, int b, int c, int d) {
  addclause(-c, a, b);
  addclause(c, -a);
  addclause(c, -b);
  addclause(-d, a);
  addclause(-d, b);
  addclause(d, -a, -b);
}

void solver::pwsplit(std::vector<int> const & a, std::vector<int> & b, std::vector<int> & c) {
  int n = a.size() / 2;
  b.resize(n);
  c.resize(n);
  for(int i = 0; i < n; i++) {
    b[i] = newvar();
    c[i] = newvar();
    comparator(a[i + i], a[i + i + 1], b[i], c[i]);
  }
}

void solver::pwmerge(std::vector<int> const & a, std::vector<int> const & b, std::vector<int> & c) {
  std::vector<int> a_next, b_next, d, e;
  int n = a.size();
  if(n == 1) {
    c.push_back(a[0]);
    c.push_back(b[0]);
    return;
  }
  a_next.resize(n / 2);
  b_next.resize(n / 2);
  for(int i = 0; i < n / 2; i++) {
    a_next[i] = a[i + i];
    b_next[i] = b[i + i];
  }
  pwmerge(a_next, b_next, d);
  for(int i = 0; i < n / 2; i++) {
    a_next[i] = a[i + i + 1];
    b_next[i] = b[i + i + 1];
  }
  pwmerge(a_next, b_next, e);
  c.resize(n + n);
  c[0] = d[0];
  for(int i = 0; i < n - 1; i++) {
    c[i + i + 1] = newvar();
    c[i + i + 2] = newvar();
    comparator(e[i], d[i + 1], c[i + i + 1], c[i + i + 2]);
  }
  c[n + n - 1] = e[n - 1];
}

void solver::pwsort(std::vector<int> const & a, std::vector<int> & d) {
  if(a.size() == 1) {
    d.push_back(a[0]);
    return;
  }
  std::vector<int> b, c, b_next, c_next;
  pwsplit(a, b, c);
  pwsort(b, b_next);
  b.clear();
  pwsort(c, c_next);
  c.clear();
  pwmerge(b_next, c_next, d);
}

void solver::pwnet(std::vector<int> vVars, int k) {
  if(vVars.size() <= k) return;
  std::vector<int> res;
  int n = clog2(vVars.size());
  while(vVars.size() != (1 << n)) {
    vVars.push_back(1);
  }
  pwsort(vVars, res);
  addclause(-res[k]);
}
