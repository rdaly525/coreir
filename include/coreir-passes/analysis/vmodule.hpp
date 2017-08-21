#ifndef VMODULE_HPP_
#define VMODULE_HPP_


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

class VWire {
  string name;
  unsigned dim;
  Type::DirKind dir;
  public :
    VWire(string field,Type* t) : name(field), dim(t->getSize()), dir(t->getDir()) {}
    VWire(Wireable* w) : VWire("",w->getType()) {
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
    VWire(string name, unsigned dim, Type::DirKind dir) : name(name), dim(dim), dir(dir) {}
    string dimstr() {
      if (dim==1) return "";
      return "["+to_string(dim-1)+":0]";
    }
    string dirstr() { return (dir==Type::DK_In) ? "input" : "output"; }
    string getName() { return name;}
};


class VModule {
  string modname;
  unordered_map<string,VWire> ports;
  unordered_set<string> params;
  unordered_map<string,string> paramDefaults;

  Generator* gen = nullptr;
  
  vector<string> stmts;
  public:
    VModule(string modname, Type* t) {
      this->modname = modname;
      Type2Ports(t,ports);
    }
    VModule(Module* m) : VModule(m->getName(),m->getType()) {
      if (!m->hasDef()) modname = m->getNamespace()->getName() + "_" + m->getName();
      this->addparams(m->getConfigParams());
      for (auto amap : m->getDefaultConfigArgs()) {
        paramDefaults[amap.first] = amap.second->toString();
      }
    }
    VModule(Generator* g) : modname(g->getNamespace()->getName()+"_"+g->getName()), gen(g) {
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
    void Type2Ports(Type* t,unordered_map<string,VWire>& ports) {
      for (auto rmap : cast<RecordType>(t)->getRecord()) {
        ports.emplace(rmap.first,VWire(rmap.first,rmap.second));
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
