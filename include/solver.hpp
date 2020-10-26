#include <vector>
#include <string>
#include <fstream>

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

  void amk(std::vector<int> const &vLits, int k) {
    pwnet(vLits, k);
  }
};

class gurobi : public solver {
public:
  std::string constraints;
  std::string objective;
  
  int newvar() override {
    nVars++;
    return nVars;
  }

  void addclause(std::vector<int> const &vLits) override {
    int c = 1;
    for(int lit : vLits) {
      if(lit < 0) {
	constraints += "-";
	c--;
      }
      constraints += "x" + std::to_string(abs(lit)) + " + ";
    }
    constraints.pop_back();
    constraints.pop_back();
    constraints += ">= " + std::to_string(c) + "\n";
  }
  void addclause(int a) override {
    constraints += "x" + std::to_string(abs(a)) + " = ";
    if(a < 0) {
      constraints += "0";
    } else {
      constraints += "1";
    }
    constraints += "\n";
  }
  void addclause(int a, int b) override {
    std::vector<int> vLits;
    vLits.push_back(a);
    vLits.push_back(b);
    addclause(vLits);
  }
  void addclause(int a, int b, int c) override {
    std::vector<int> vLits;
    vLits.push_back(a);
    vLits.push_back(b);
    vLits.push_back(c);
    addclause(vLits);
  }

  bool solve() override {
    {
      std::ofstream f("_tbplace.lp");
      f << objective;
      f << "subject to\n";
      f << constraints;
      f << "binary\n";
      for(int i = 0; i < nVars; i++) {
	f << "x" << i+1 << std::endl;
      }
      f << "end";
      f.close();
    }
    
    std::string cmd = "gurobi_cl ResultFile=\"_tbplace.sol\" _tbplace.lp";
    system(cmd.c_str());

    model.clear();
    model.resize(nVars + 1);

    {
      std::ifstream f("_tbplace.sol");
      std::string str;
      while(std::getline(f, str)) {
	if(str.empty()) {
	  continue;
	}
	if(str[0] != 'x') {
	  continue;
	}
	int pos = str.find(' ');
	int v = std::stoi(str.substr(1, pos - 1));
	model[v] = str[pos + 1] == '1';
      }
    }
    
    return true;
  }

  void amk(std::vector<int> const &vLits, int k) {
    if(vLits.size() <= k) {
      return;
    }
    int c = k;
    for(int lit : vLits) {
      if(lit < 0) {
	constraints += "-";
	c--;
      }
      constraints += "x" + std::to_string(abs(lit)) + " + ";
    }
    constraints.pop_back();
    constraints.pop_back();
    constraints += "<= " + std::to_string(c) + "\n";
  }
  
};
