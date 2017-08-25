#include "coreir.h"
#include "coreir-passes/analysis/vmtmodule.hpp"
#include "coreir-passes/analysis/vmtoperators.hpp"
#include "coreir-passes/analysis/vmt.h"

using namespace CoreIR;
using namespace Passes;

namespace {

  string CLOCK = "clk";
  
  std::vector<string> check_interface_variable(std::vector<string> variables, VmtBVVar var, VMTModule* smod) {
  if ( find(variables.begin(), variables.end(), var.getName()) == variables.end() ) {
      variables.push_back(var.getName());
      smod->addVarDec(VmtBVVarDec(VmtBVVarGetCurr(var)));
      smod->addNextVarDec(VmtBVVarDec(VmtBVVarGetNext(var)));
      smod->addInitVarDec(VmtBVVarDec(VmtBVVarGetInit(var)));
      // smod->addStmt(";; ADDING missing variable: " +var.getName()+"\n");
      if (var.getName().find(CLOCK) != string::npos) {
        smod->addStmt(";; START module declaration for signal '" + var.getName());
        smod->addStmt(VMTClock(std::make_pair("", var)));
        smod->addStmt(";; END module declaration\n");
      }
    }
  return variables;
  }

}

std::string Passes::VMT::ID = "vmt";
bool Passes::VMT::runOnInstanceGraphNode(InstanceGraphNode& node) {

  //Create a new VMTmodule for this node
  Instantiable* i = node.getInstantiable();
  if (auto g = dyn_cast<Generator>(i)) {
    this->modMap[i] = new VMTModule(g);
    this->external.insert(i);
    return false;
  }
  Module* m = cast<Module>(i);
  VMTModule* smod = new VMTModule(m);
  modMap[i] = smod;
  if (!m->hasDef()) {
    this->external.insert(i);
    return false;
  }

  ModuleDef* def = m->getDef();

  static std::vector<string> variables; 
  string tab = "  ";
  for (auto imap : def->getInstances()) {
    string iname = imap.first;
    Instance* inst = imap.second;
    Instantiable* iref = imap.second->getInstantiableRef();
    // do not add comment for no ops
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt(";; START module declaration for instance '" + imap.first + "' (Module "+ iref->getName() + ")");
    }
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      VmtBVVar var = VmtBVVar(iname+"_"+rmap.first,rmap.second);
      variables.push_back(var.getName());
      smod->addVarDec(VmtBVVarDec(VmtBVVarGetCurr(var)));
      smod->addNextVarDec(VmtBVVarDec(VmtBVVarGetNext(var)));
      smod->addInitVarDec(VmtBVVarDec(VmtBVVarGetInit(var)));
    }
    ASSERT(modMap.count(iref),"DEBUG ME: Missing iref");
    smod->addStmt(modMap[iref]->toInstanceString(inst));
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt(";; END module declaration\n");
    }
  }

  smod->addStmt(";; START connections definition");
  for (auto con : def->getConnections()) {
    Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
    Wireable* right = left==con.first ? con.second : con.first;
    VmtBVVar vleft(left);
    VmtBVVar vright(right);

    variables = check_interface_variable(variables, vleft, smod);
    variables = check_interface_variable(variables, vright, smod);
    
    smod->addStmt(VMTAssign(vleft, vright));
  }
  smod->addStmt(";; END connections definition\n");

  return false;
}

void Passes::VMT::writeToStream(std::ostream& os) {

  os << "(set-logic QF_BV)" << endl;
  
  // Print variable declarations

  os << ";; Init Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) {
      os << mmap.second->toInitVarDecString() << endl;
    }
  }
  
  os << ";; Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) {
      os << mmap.second->toVarDecString() << endl;
    }
  }

  os << ";; Next Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) {
      os << mmap.second->toNextVarDecString() << endl;
    }
  }

  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) {
      os << mmap.second->toString() << endl;
    }
  }


}
