#include "coreir.h"
#include "coreir-passes/firrtl.hpp"

using namespace CoreIR;


string SelectPath2firrtl(SelectPath path) {
  cout << SelectPath2Str(path) << endl;
  if (path[0]=="self") {
    path.pop_front();
  }
  vector<string> pathred;
  for (auto s : path) {
    if (isNumber(s)) {
      pathred.push_back("["+s+"]");
    }
    else {
      pathred.push_back(s);
    }
    cout << "H:" << s << endl;
  }
  return join(pathred.begin(),pathred.end(),string("."));
}

string type2firrtl(Type* t, bool noWidths=false) {
  if (auto rt = dyn_cast<RecordType>(t)) {
    vector<string> sels;
    if (!rt->isMixed()) {
      for (auto rec : rt->getRecord()) {
        sels.push_back(rec.first + " : " + type2firrtl(rec.second));
      }
    }
    else {
      //for (auto rec : rt->getRecord()) {
      //  string pre = "";
      //  if (rec.first
      ASSERT(0,"NYI")
    }
    return join(sels.begin(),sels.end(),string(", "));
  }
  else if (auto at = dyn_cast<ArrayType>(t)) {
    Type* et = at->getElemType();
    if (et->isBaseType()) {
      if (noWidths) return "UInt";
      return "UInt<" + to_string(at->getLen()) + ">";
    }
    else {
      return type2firrtl(et) + "[" + to_string(at->getLen()) + "]";
    }
  }
  else if (t->isBaseType()) {
    return "UInt<1>";
  }
  else {
    assert(0);
  }
}

struct FModule {
  string name;
  RecordType* rt;
  bool noWidths;
  vector<string> stmts;
  FModule(string name, Type* t, bool noWidths=false) : name(name), noWidths(noWidths) {
    if (! (this->rt = dyn_cast<RecordType>(t))) {
      assert(0);
    }
  }
  void addStmt(string stmt) {
    stmts.push_back(stmt);
  }
  string toString() {
    vector<string> lines;
    lines.push_back("  module " + this->name + " :");
    for (auto rec : rt->getRecord()) {
      string s = "    ";
      if (rec.second->isInput()) {
        s = s + "input ";
      }
      else if(rec.second->isOutput()) {
        s = s + "output ";
      }
      else {
        rt->print();
        ASSERT(0,"NYI");
      }
      s = s + rec.first + " : " + type2firrtl(rec.second);
      lines.push_back(s);
    }
    for (auto s : this->stmts) {
      lines.push_back("    " + s);
    }
    return join(lines.begin(),lines.end(),string("\n"));
  }
};

string op2firrtl(string op) {
  //TODO 
  return op;
}

void stdlib2firrtl(Instantiable* i,FModule& fm) {
  if (i->getName()=="mux") {
    fm.addStmt("out <= mux(sel,in[0],in[1])");
  }
  else if (i->getName()=="reg") {
    ASSERT(0,"NYI");
  }
  else if (opmap["binary"].count(i->getName()) 
     || opmap["binaryReduce"].count(i->getName())) {
      fm.addStmt("out <= " + op2firrtl(i->getName()) + "(in[0],in[1])");
  }
  else {
    assert(opmap["unary"].count(i->getName())
        || opmap["unaryReduce"].count(i->getName()));
    
    fm.addStmt("out <= " + op2firrtl(i->getName()) + "(in)");
  }
}

bool Firrtl::runOnInstanceGraphNode(InstanceGraphNode& node) {
  cout << "H1" << endl;
  auto i = node.getInstantiable();
  string name = i->getName();
  bool isStdlib = i->getNamespace()->getName() == "stdlib";
  if (isStdlib) {
    name = "coreir_" + i->getName();
  }
  cout << "H2" << endl;
  cout << i->toString() << endl;
  assert(nameMap.count(i)==0);
  cout << "HERE!" << endl;
  nameMap[i] = name;
  cout << "HERE2!" << endl;
  FModule* fm;
  if (isStdlib) {
  cout << "H3" << endl;
    //This ugliness is getting an example of a type for stdlib generator
    Type* t = cast<Generator>(i)->getTypeGen()->createType(i->getContext(),{{"width",i->getContext()->argInt(5)}});
    fm = new FModule(name,t,true);
    stdlib2firrtl(i,*fm);
  cout << "H4" << endl;
  }
  else {
    //General case.
    Module* m = cast<Module>(i);
    ASSERT(m->hasDef(),"NYI external modules");
    ModuleDef* def = m->getDef();
    fm = new FModule(name,m->getType());
    
    //First add all instances
    for (auto instmap : def->getInstances()) {
      string mname = nameMap[instmap.second->getInstantiableRef()];
      string iname = instmap.second->getInstname();
      fm->addStmt("inst " + iname + " of " + mname);
    }
    //Then add all connections
    auto dm = m->newDirectedModule();
    for (auto dcon : dm->getConnections()) {
      fm->addStmt(def->sel(dcon->getSnk())->toString() + " <= " + def->sel(dcon->getSrc())->toString());
    }
  }
  fmods.push_back(fm->toString());
  return false;
}

//FOR now just output in print
void Firrtl::print() {
  cout << "Circuit MyCircuit : " << endl;
  for (auto smod : fmods) {
    cout << smod << endl;
  }
}


















