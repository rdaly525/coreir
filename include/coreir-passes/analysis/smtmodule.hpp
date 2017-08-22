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

class SMTWire {
  string name;
  unsigned dim;
  Type::DirKind dir;
  public :
    SMTWire(string field,Type* t) : name(field), dim(t->getSize()), dir(t->getDir()) {}
    SMTWire(Wireable* w) : SMTWire("",w->getType()) {
      SelectPath sp = w->getSelectPath();
      if (sp.size()==3) {
        ASSERT(dim==1 && !isNumber(sp[1]) && isNumber(sp[2]),"DEBUG ME:");
        name = sp[1]+"["+sp[2]+"]";
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
    }
    SMTWire(string name, unsigned dim, Type::DirKind dir) : name(name), dim(dim), dir(dir) {}
    string dimstr() {
      if (dim==1) return "";
      return "["+to_string(dim-1)+":0]";
    }
    string dirstr() { return (dir==Type::DK_In) ? "input" : "output"; }
    string getName() { return name;}
};


class SMTModule {
  string modname;
  unordered_map<string,SMTWire> ports;
  unordered_set<string> params;
  unordered_map<string,string> paramDefaults;

  Generator* gen = nullptr;
  
  vector<string> stmts;
  public:
    SMTModule(string modname, Type* t) {
      this->modname = modname;
      Type2Ports(t,ports);
    }
    SMTModule(Module* m) : SMTModule(m->getName(),m->getType()) {
      const json& jmeta = m->getMetaData();
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
      if (jmeta.count("verilog") && jmeta["verilog"].count("prefix")) {
        modname = jmeta["verilog"]["prefix"].get<string>() + g->getName();
      }
      this->addparams(g->getGenParams());
      this->addparams(g->getConfigParams());
    }
    void addStmt(string stmt) { stmts.push_back(stmt); }
    string toCommentString() {
      return "//Module: " + modname + " defined externally";
    }
    string toString();
    string toInstanceString(Instance* inst);
  private :
    void Type2Ports(Type* t,unordered_map<string,SMTWire>& ports) {
      for (auto rmap : cast<RecordType>(t)->getRecord()) {
        ports.emplace(rmap.first,SMTWire(rmap.first,rmap.second));
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
