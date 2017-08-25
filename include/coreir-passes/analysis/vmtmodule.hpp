#ifndef VMTMODULE_HPP_
#define VMTMODULE_HPP_


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

class VmtBVVar {
  string name;
  unsigned dim;
  string idx;
  bool need_extract = false;
  Type::DirKind dir;
  public :
    VmtBVVar(string field,Type* t) : name(field), dim(t->getSize()), dir(t->getDir()) {}
    VmtBVVar(Wireable* w) : VmtBVVar("",w->getType()) {
      SelectPath sp = w->getSelectPath();
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
    }
  bool operator==(const VmtBVVar &other) const
  { return (name.compare(other.name) == 0);
  }  
    VmtBVVar(string name, unsigned dim, Type::DirKind dir) : name(name), dim(dim), dir(dir) {}
    string dimstr() {return to_string(dim);}
    string dirstr() { return (dir==Type::DK_In) ? "input" : "output"; }
    string getExtractName() { return need_extract ? "((_ extract " + idx + " " + idx + ") " + name + ")" : name;}
    string getName() { return name;}
    string setName(string name) { return this->name = name;}
};


class VMTModule {
  string modname;
  unordered_map<string,VmtBVVar> ports;
  unordered_set<string> params;
  unordered_map<string,string> paramDefaults;

  Generator* gen = nullptr;
  
  vector<string> stmts;
  vector<string> vardecs;
  vector<string> nextvardecs;
  vector<string> initvardecs;
  public:
    VMTModule(string modname, Type* t) {
      this->modname = modname;
      Type2Ports(t,ports);
    }
    VMTModule(Module* m) : VMTModule(m->getName(),m->getType()) {
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
    VMTModule(Generator* g) : modname(g->getName()), gen(g) {
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
    void addNextVarDec(string vd) { nextvardecs.push_back(vd); }
    void addInitVarDec(string vd) { initvardecs.push_back(vd); }
    string toCommentString() {
      return "//Module: " + modname + " defined externally";
    }
    string toString();
    string toVarDecString();
    string toNextVarDecString();
    string toInitVarDecString();
    string toInstanceString(Instance* inst);
  private :
    void Type2Ports(Type* t,unordered_map<string,VmtBVVar>& ports) {
      for (auto rmap : cast<RecordType>(t)->getRecord()) {
        ports.emplace(rmap.first,VmtBVVar(rmap.first,rmap.second));
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
