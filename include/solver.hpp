#include <vector>

#include <simp/SimpSolver.h>

class solver {
public:
  int nVars = 0;
  std::vector<bool> model;

  virtual ~solver() {};

  virtual int newvar() = 0;

  virtual void addclause(std::vector<int> const &vLits) = 0;
  virtual void addclause(int a) = 0;
  virtual void addclause(int a, int b) = 0;
  virtual void addclause(int a, int b, int c) = 0;

  virtual bool solve() = 0;
  
  void bimander(std::vector<int> const &vLits, int nbim);
  void comparator(int a, int b, int c, int d);
  void pwsplit(std::vector<int> const & a, std::vector<int> & b, std::vector<int> & c);
  void pwmerge(std::vector<int> const & a, std::vector<int> const & b, std::vector<int> & c);
  void pwsort(std::vector<int> const & a, std::vector<int> & d);
  void pwnet(std::vector<int> vVars, int k);
};

class glucose : public solver {
  Glucose::SimpSolver * p;

public:
  glucose() {
    p = new Glucose::SimpSolver;
    //p->setIncrementalMode();
    //p->use_elim = 0;
  };
  ~glucose() {
    delete p;
  }
  
  int newvar() override {
    p->newVar();
    nVars++;
    return nVars;
  };
  
  void addclause(int a) override {
    p->addClause(Glucose::mkLit(abs(a) - 1, a < 0));
  }
  void addclause(int a, int b) override {
    p->addClause(Glucose::mkLit(abs(a) - 1, a < 0), Glucose::mkLit(abs(b) - 1, b < 0));
  }
  void addclause(int a, int b, int c) override {
    p->addClause(Glucose::mkLit(abs(a) - 1, a < 0), Glucose::mkLit(abs(b) - 1, b < 0), Glucose::mkLit(abs(c) - 1, c < 0));
  }
  void addclause(std::vector<int> const &vLits) override {
    Glucose::vec<Glucose::Lit> gLits;
    for(int a: vLits) {
      gLits.push(Glucose::mkLit(abs(a)-1, a < 0));
    }
    p->addClause(gLits);
  }

  bool solve() override {
    model.clear();
    int status = p->solve();
    if(status == 0) {
      return false;
    }
    model.push_back(false); // dummy
    for(int i = 0; i < nVars; i++) {
      if(p->model[i] == l_True) {
	model.push_back(true);
      }
      else {
	model.push_back(false);
      }
    }
    return true;
  }
};

/*class gurobi : public solver {
  
  };*/
