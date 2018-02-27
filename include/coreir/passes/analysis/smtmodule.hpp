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
using namespace std;

class SmtBVVar {
  string instname = "";
  string portname;
  string name;
  unsigned dim;
  string idx;
  string fullname = "";
  bool need_extract = false;
  Type::DirKind dir;
public :
  SmtBVVar() = default;
  SmtBVVar(string instname, string field,Type* t) :
    instname(instname), portname(field), dim(t->getSize()), dir(t->getDir())     {
    name = (instname == "" ? "" : instname + "$") + portname;
    fullname = field+name;
  }
  SmtBVVar(Wireable* w) : SmtBVVar("","",w->getType()) {
    SelectPath sp = w->getSelectPath();
    if (sp.size()==3) {
      ASSERT(dim==1 && !isNumber(sp[1]) && isNumber(sp[2]),"DEBUG ME:");
      // extract the necessary dimension
      need_extract = true;
      idx = sp[2];
      portname = sp[1];
    }
    else if (sp.size()==2) {
      ASSERT(!isNumber(sp[1]),"DEBUG ME:");
      portname = sp[1];
    }
    else {
      assert(0);
    }

    if (sp[0] != "self") {
      instname = sp[0];
    }

    name = (instname == "" ? "" : instname + "$") + portname;
    fullname = name;
  }
  bool operator==(const SmtBVVar &other) const
  { return (name.compare(other.name) == 0);
  }
  SmtBVVar(string instname, string portname, unsigned dim, Type::DirKind dir) :
    instname(instname), portname(portname), dim(dim), dir(dir) {}
  string dimstr() {return to_string(dim);}
  string dirstr() { return (dir==Type::DK_In) ? "input" : "output"; }
  string getExtractName() { return need_extract ? "((_ extract " + idx + " " + idx + ") " + getName() + ")" : getName();}
  string getName() { return name;}
  string getFullName() { return fullname;}
  string setName(string name) { return this->name = name;}
  string getPortName() {return portname;}
};


class SMTModule {
  string modname;
  vector<SmtBVVar> ports;
  unordered_set<string> params;
  unordered_map<string,string> paramDefaults;

  bool instantiated = false;
  Generator* gen = nullptr;

  vector<string> stmts;
  vector<string> vardecs;
  vector<string> nextvardecs;
  vector<string> initvardecs;
public:
  // Don't support this constructor unless needed
  // Deprecating Type2Ports
  SMTModule(string modname, Type* t) {
    this->modname = modname;
    Type2Ports(t, ports);
  }
  SMTModule(Module* m) : SMTModule(m->getName(),m->getType()) {
    string ns;
    if(m->isGenerated()) {
      ns = m->getGenerator()->getNamespace()->getName();
    }
    else
    {
      ns = m->getNamespace()->getName();
    }
    this->modname = ns + "." + m->getName();
    const json& jmeta = m->getMetaData();
    // still using verilog prefixes -- should be okay
    if (jmeta.count("verilog") && jmeta["verilog"].count("prefix")) {
      modname = jmeta["verilog"]["prefix"].get<string>() + m->getName();
    }

    this->addParams(params,m->getModParams());
    this->addDefaults(paramDefaults,m->getDefaultModArgs());
  }
  SMTModule(Generator* g) : modname(g->getNamespace()->getName() + "." + g->getName()), gen(g) {
    const json& jmeta = g->getMetaData();
    // still using verilog prefixes -- should be fine
    if (jmeta.count("verilog") && jmeta["verilog"].count("prefix")) {
      cout << "verilog prefix tag" << jmeta["verilog"]["prefix"].get<string>() << endl;
      modname = jmeta["verilog"]["prefix"].get<string>() + g->getName();
    }
    this->addParams(params,g->getGenParams());
    this->addDefaults(paramDefaults,g->getDefaultGenArgs());
    //    this->addparams(g->getConfigParams());
  }
  void addStmt(string stmt) { stmts.push_back(stmt); }
  void addPort(SmtBVVar v) {ports.push_back(v);}
  void addVarDec(string vd) { vardecs.push_back(vd); }
  void addNextVarDec(string vd) { nextvardecs.push_back(vd); }
  void addInitVarDec(string vd) { initvardecs.push_back(vd); }
  string toCommentString() {
    return "//Module: " + modname + " defined externally";
  }
  void instantiate() {instantiated=true;}
  bool isInstantiated() {return instantiated;}
  string toString();
  string toVarDecString();
  string toNextVarDecString();
  string toInitVarDecString();
  string toInstanceString(Instance* inst, string path);
private :
  void Type2Ports(Type* t,vector<SmtBVVar>& ports) {
    for (auto rmap : cast<RecordType>(t)->getRecord()) {
      ports.push_back(SmtBVVar("",rmap.first,rmap.second));
    }
  }
  void addPortsFromGen(Instance* inst) {
    Module *m = inst->getModuleRef();
    ASSERT (m->isGenerated(), "Module not generated");
    Type* t = gen->getTypeGen()->getType(inst->getModuleRef()->getGenArgs());
    for (auto rmap : cast<RecordType>(t)->getRecord()) {
      ports.push_back(SmtBVVar(inst->getInstname(), rmap.first, rmap.second));
    }
  }
  void addParams(unordered_set<string>& sps, Params ps) {
    for (auto p : ps) {
      ASSERT(params.count(p.first)==0,"NYI Cannot have duplicate params");
      sps.insert(p.first);
    }
  }
  void addDefaults(unordered_map<string,string> sm, Values ds) {
    for (auto dpair : ds) {
      sm[dpair.first] = toConstString(dpair.second);
    }
  }
  std::string toConstString(Value* v) {
    if (auto av = dyn_cast<Arg>(v)) {
      return av->getField();
    }
    else if (auto iv = dyn_cast<ConstInt>(v)) {
      return iv->toString();
    }
    else if (auto bv = dyn_cast<ConstBool>(v)) {
      return std::to_string(uint(bv->get()));
    }
    else if (auto bvv = dyn_cast<ConstBitVector>(v)) {
      BitVector bv = bvv->get();
      return std::to_string(bv.bitLength())+"'d"+std::to_string(bv.to_type<uint64_t>());
    }
    assert(0);
  }

};

#endif
