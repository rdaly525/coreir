#include "coreir.h"
#include "coreir/passes/analysis/firrtl.h"

using namespace std;
using namespace CoreIR;

class FModule {
  string name;
  vector<string> io;
  vector<string> stmts;
  public : 
    FModule(Instantiable* iref) : name(iref->getName()) {
      checkJson(iref->getMetaData());
      if (isa<Generator>(iref)) {
        ASSERT(this->hasDef(),"NYI generators without a firrtl def");
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
      }
    }
    bool hasDef() {return io.size()>0 && stmts.size()>0;}
    void addStmt(string stmt) {
      stmts.push_back(stmt);
    }
    void addIO(RecordType* rt) {
      for (auto rpair : rt->getRecord()) {
        Type* t = rpair.second;
        //Assumes mixed types are outputs
        addStmt(string(t->isInput() ? "input" : "output") + " " + rpair.first + " " + type2firrtl(t,t->isInput()));
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
  else if (t->isBaseType()) {
    return "UInt<1>";
  }
  else {
    assert(0);
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
  if (isa<Generator>(i)) {
    ASSERT(fm.hasDef(),"NYI: generators in firrtl without def");
    fmods.push_back(fm.toString());
    return false;
  }
  Module* m = cast<Module>(i);
  ASSERT(m->hasDef(),"NYI external modules");
  ModuleDef* def = m->getDef();
  
  //First add all instances
  for (auto instmap : def->getInstances()) {
    string mname = nameMap[instmap.second->getInstantiableRef()];
    string iname = instmap.second->getInstname();
    fm.addStmt("inst " + iname + " of " + mname);
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






