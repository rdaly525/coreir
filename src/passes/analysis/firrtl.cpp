#include "coreir.h"
#include "coreir/passes/analysis/firrtl.h"

using namespace std;
using namespace CoreIR;

class FModule {
  Context* c;
  string name;
  vector<string> io;
  vector<string> params;
  vector<string> stmts;
  public : 
    FModule(Instantiable* iref) : c(iref->getContext()), name(iref->getName()) {
      checkJson(iref->getMetaData());
      if (isa<Generator>(iref)) {
        ASSERT(this->hasDef(),"NYI generators without a firrtl def " + iref->toString());
      }
      else {
        Module* m = cast<Module>(iref);
        if (io.size()==0) addIO(cast<RecordType>(m->getType()));
      }
    }
    string getName() { return name;}
    void checkJson(json jmeta) {
      if (jmeta.count("firrtl") ) {
        if (jmeta["firrtl"].count("prefix")) {
          this->name = jmeta["firrtl"]["prefix"].get<std::string>() + this->name;
        }
        if (jmeta["firrtl"].count("definition")) {
          for (auto stmt : jmeta["firrtl"]["definition"].get<vector<string>>()) {
            addStmt(stmt);
          }
        }
        if (jmeta["firrtl"].count("interface")) {
          addIO(jmeta["firrtl"]["interface"].get<std::vector<std::string>>());
        }
        if (jmeta["firrtl"].count("parameters")) {
          this->params = (jmeta["firrtl"]["parameters"].get<std::vector<std::string>>());
        }
      }
    }
    vector<string> getParams() { return params;}
    bool hasDef() {return io.size()>0 && stmts.size()>0;}
    void addStmt(string stmt) {
      stmts.push_back(stmt);
    }
    void addIO(RecordType* rt) {
      for (auto rpair : rt->getRecord()) {
        Type* t = rpair.second;
        //Assumes mixed types are outputs
        addStmt(string(t->isInput() ? "input" : "output") + " " + rpair.first + " : " + type2firrtl(t,t->isInput()));
      }
    }
    void addIO(vector<string> ios) {
      for (auto it : ios) io.push_back(it);
    }
    string type2firrtl(Type* t, bool isInput);
    string toString() {
      vector<string> lines;
      lines.push_back("  module " + this->name + " :");
      for (auto s : this->io) {
        lines.push_back("    " + s);
      }
      for (auto s : this->stmts) {
        lines.push_back("    " + s);
      }
      return join(lines.begin(),lines.end(),string("\n"));
    }
};

string FModule::type2firrtl(Type* t, bool isInput) {
  if (auto rt = dyn_cast<RecordType>(t)) {
    vector<string> sels;
    if (!rt->isMixed()) {
      for (auto rec : rt->getRecord()) {
        sels.push_back(rec.first + " : " + type2firrtl(rec.second,isInput));
      }
    }
    else {
      ASSERT(0,"NYI");
    }
    return join(sels.begin(),sels.end(),string(", "));
  }
  else if (auto at = dyn_cast<ArrayType>(t)) {
    Type* et = at->getElemType();
    if (et->isBaseType()) {
      return "UInt<" + to_string(at->getLen()) + ">";
    }
    else {
      return type2firrtl(et,isInput) + "[" + to_string(at->getLen()) + "]";
    }
  }
  else if (auto nt = dyn_cast<NamedType>(t)) {
    if (nt == c->Named("coreir.clk") || nt == c->Named("coreir.clkIn")) return "Clock";
    else if (nt == c->Named("coreir.rst") || nt == c->Named("coreir.rstIn")) return "UInt<1>";
    else ASSERT(0,"NYI: " + nt->toString());
  }
  else if (t->isBaseType()) {
    return "UInt<1>";
  }
  else {
    ASSERT(0,"DEBUGME: " +t->toString());
  }
}

string sp2Str(SelectPath sp) {
  string ret = sp[0];
  sp.pop_front();
  for (auto s : sp) {
    if (isNumber(s)) ret  = ret +"[" + s + "]";
    else ret = ret + "." + s;
  }
  return ret;
}

string Passes::Firrtl::ID = "firrtl";
bool Passes::Firrtl::runOnInstanceGraphNode(InstanceGraphNode& node) {
  auto i = node.getInstantiable();
 
  FModule fm(i);
  ASSERT(nameMap.count(i)==0,"DEBUG ME");
  nameMap[i] = fm.getName();
  if (fm.getParams().size()) {
    this->paramMap[i] = fm.getParams();
  }
  if (isa<Generator>(i)) {
    ASSERT(fm.hasDef(),"NYI: generators in firrtl without def");
    fmods.push_back(fm.toString());
    return false;
  }
  Module* m = cast<Module>(i);
  ASSERT(m->hasDef(),"NYI external modules");
  ModuleDef* def = m->getDef();
  
  //First add all instances
  for (auto instpair : def->getInstances()) {
    Instance* inst = instpair.second;
    string iname = instpair.first;
    string mname = nameMap[inst->getInstantiableRef()];
    fm.addStmt("inst " + iname + " of " + mname);
    if (paramMap.count(inst->getInstantiableRef())) {
      auto params = paramMap[inst->getInstantiableRef()];
      Values args = inst->getGenArgs();
      mergeValues(args,inst->getModArgs());
      for (auto p : params) {
        ASSERT(args.count(p),"Missing param " + p + " for " + Inst2Str(inst) + "\n  From: "+Values2Str(args));
        Value* v = args[p];
        if (auto aint = dyn_cast<ConstInt>(v)) {
          fm.addStmt(iname + "." + p + " <= " + aint->toString());
        }
        else if (auto abv = dyn_cast<ConstBitVector>(v)) {
          fm.addStmt(iname + "." + p + " <= " + abv->toString());
        }
        else {
          ASSERT(0,"NYI: Value " +p+ " cannot be " + v->toString());
        }
      }
    }
  }
  //Then add all connections
  auto dm = m->newDirectedModule();
  for (auto dcon : dm->getConnections()) {
    SelectPath src = dcon->getSrc();
    if (src[0] == "self") src.pop_front();
    SelectPath snk = dcon->getSnk();
    if (snk[0] == "self") snk.pop_front();
    fm.addStmt(sp2Str(snk) + " <= " + sp2Str(src));
  }
  fmods.push_back(fm.toString());
  
  return false;
}

void Passes::Firrtl::writeToStream(std::ostream& os) {
  os << "Circuit MyCircuit : " << endl;
  for (auto smod : fmods) {
    os << smod << endl;
  }
}






