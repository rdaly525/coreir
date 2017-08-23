#ifndef SMTMODULE_HPP_
#define SMTMODULE_HPP_


//What I need to represent
//
//Wire(string name, int bits)
//
//ModuleDec((Wire w,string dir)* puts,stmt* stmsts)
//Stmt = string
//     | WireDec(Wire w)
//     | Assigns(string left, string right)
//     | Instance(string modname,(Wire l, Wire r)*)
//
//Expr = string
//     | Wire


using namespace CoreIR; //TODO get rid of this

class SmtBVVar {
  string name;
  unsigned dim;
  Type::DirKind dir;
  public :
    SmtBVVar(string field,Type* t) : name(field), dim(t->getSize()), dir(t->getDir()) {}
    SmtBVVar(Wireable* w) : SmtBVVar("",w->getType()) {
      SelectPath sp = w->getSelectPath();
      bool need_extract = false;
      string idx;
      if (sp.size()==3) {
        ASSERT(dim==1 && !isNumber(sp[1]) && isNumber(sp[2]),"DEBUG ME:");
	// extract the necessary dimension
	need_extract = true;
	idx = sp[2];
        name = sp[1];
      }
      else if (sp.size()==2) {
        ASSERT(!isNumber(sp[1]),"DEBUG ME:");
        name = sp[1];
      }
      else {
        assert(0);
      }

      if (sp[0] != "self") {
        name = sp[0]+ "_" + name;
      }

      if (need_extract){
	name = "((_ extract " + idx + " " + idx + ") " + name + ")";
      }
    }
    SmtBVVar(string name, unsigned dim, Type::DirKind dir) : name(name), dim(dim), dir(dir) {}
    string dimstr() {return to_string(dim);}
    string dirstr() { return (dir==Type::DK_In) ? "input" : "output"; }
    string getName() { return name;}
};


class SMTModule {
  string modname;
  unordered_map<string,SmtBVVar> ports;
  unordered_set<string> params;
  unordered_map<string,string> paramDefaults;

  Generator* gen = nullptr;
  
  vector<string> stmts;
  vector<string> vardecs;
  vector<string> nexvardecs;
  public:
    SMTModule(string modname, Type* t) {
      this->modname = modname;
      Type2Ports(t,ports);
    }
    SMTModule(Module* m) : SMTModule(m->getName(),m->getType()) {
      const json& jmeta = m->getMetaData();
      // still using verilog prefixes -- should be okay
      if (jmeta.count("verilog") && jmeta["verilog"].count("prefix")) {
        modname = jmeta["verilog"]["prefix"].get<string>() + m->getName();
      }

      this->addparams(m->getConfigParams());
      for (auto amap : m->getDefaultConfigArgs()) {
        paramDefaults[amap.first] = amap.second->toString();
      }
    }
    SMTModule(Generator* g) : modname(g->getName()), gen(g) {
      const json& jmeta = g->getMetaData();
      // still using verilog prefixes -- should be fine
      if (jmeta.count("verilog") && jmeta["verilog"].count("prefix")) {
        modname = jmeta["verilog"]["prefix"].get<string>() + g->getName();
      }
      this->addparams(g->getGenParams());
      this->addparams(g->getConfigParams());
    }
    void addStmt(string stmt) { stmts.push_back(stmt); }
    void addVarDec(string vd) { vardecs.push_back(vd); }
    void addNexVarDec(string vd) { nexvardecs.push_back(vd); }
    string toCommentString() {
      return "//Module: " + modname + " defined externally";
    }
    string toString();
    string toVarDecString();
    string toNexVarDecString();
    string toInstanceString(Instance* inst);
  private :
    void Type2Ports(Type* t,unordered_map<string,SmtBVVar>& ports) {
      for (auto rmap : cast<RecordType>(t)->getRecord()) {
        ports.emplace(rmap.first,SmtBVVar(rmap.first,rmap.second));
      }
    }
    void addparams(Params ps) { 
      for (auto p : ps) {
        ASSERT(params.count(p.first)==0,"NYI Cannot have duplicate params");
        params.insert(p.first); 
      }
    }
};

#endif
