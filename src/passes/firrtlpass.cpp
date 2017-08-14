#include "coreir.h"
#include "coreir-passes/firrtl.hpp"
#include <iostream>
#include <fstream>

using namespace CoreIR;


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
  string type2firrtl(Type* t);
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

string FModule::type2firrtl(Type* t) {
  if (auto rt = dyn_cast<RecordType>(t)) {
    vector<string> sels;
    if (!rt->isMixed()) {
      for (auto rec : rt->getRecord()) {
        sels.push_back(rec.first + " : " + type2firrtl(rec.second));
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
  else if (i->getName()=="const") {
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
  auto i = node.getInstantiable();
  string name = i->getName();
  bool isStdlib = i->getNamespace()->getName() == "stdlib";
  if (!isStdlib && isa<Generator>(i)) {
    if (node.getInstanceList().size()>0) {
      ASSERT(0,"Cannot deal with Instantiated generators");
    }
    return false;
  }
  
  if (isStdlib) {
    name = "coreir_" + i->getName();
  }
  //TODO sometimes failing here!
  ASSERT(nameMap.count(i)==0,i->getName());
  nameMap[i] = name;
  FModule* fm;
  if (isStdlib) {
    //This ugliness is getting an example of a type for stdlib generator
    //The 5 does not matter because I am throwing away widths anyways
    Type* t = cast<Generator>(i)->getTypeGen()->createType(i->getContext(),{{"width",i->getContext()->argInt(5)}});
    fm = new FModule(name,t,true);
    stdlib2firrtl(i,*fm);
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
      //TODO Deal with consts, regs, shift
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

void Firrtl::writeToFile(string filename) {
  std::fstream file(filename,std::ostream::out);
  file << "Circuit MyCircuit : " << endl;
  for (auto smod : fmods) {
    file << smod << endl;
  }
}


















