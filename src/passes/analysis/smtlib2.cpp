#include "coreir.h"
#include "coreir/passes/analysis/smtmodule.hpp"
#include "coreir/passes/analysis/smtoperators.hpp"
#include "coreir/passes/analysis/smtlib2.h"

using namespace CoreIR;
using namespace Passes;

namespace {

  string CLOCK = "clk";
  
  std::vector<string> check_interface_variable(std::vector<string> variables, SmtBVVar var, SMTModule* smod) {
  if ( find(variables.begin(), variables.end(), var.getName()) == variables.end() ) {
      variables.push_back(var.getName());
      smod->addVarDec(SmtBVVarDec(SmtBVVarGetCurr(var)));
      smod->addNextVarDec(SmtBVVarDec(SmtBVVarGetNext(var)));
      smod->addInitVarDec(SmtBVVarDec(SmtBVVarGetInit(var)));
      // smod->addStmt(";; ADDING missing variable: " +var.getName()+"\n");
      if (var.getName().find(CLOCK) != string::npos) {
        smod->addStmt(";; START module declaration for signal '" + var.getName());
        smod->addStmt(SMTClock("", var));
        smod->addStmt(";; END module declaration\n");
      }
    }
  return variables;
  }

}

std::string Passes::SmtLib2::ID = "smtlib2";
bool Passes::SmtLib2::runOnInstanceGraphNode(InstanceGraphNode& node) {

  //Create a new SMTmodule for this node
  Instantiable* i = node.getInstantiable();
  if (auto g = dyn_cast<Generator>(i)) {
    this->modMap[i] = new SMTModule(g);
    this->external.insert(i);
    return false;
  }
  Module* m = cast<Module>(i);
  SMTModule* smod = new SMTModule(m);
  modMap[i] = smod;
  if (!m->hasDef()) {
    this->external.insert(i);
    return false;
  }

  ModuleDef* def = m->getDef();

  static std::vector<string> variables; 
  for (auto imap : def->getInstances()) {
    string iname = imap.first;
    Instance* inst = imap.second;
    Instantiable* iref = imap.second->getInstantiableRef();
    // do not add comment for no ops
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt(";; START module declaration for instance '" + imap.first + "' (Module "+ iref->getName() + ")");
    }
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      SmtBVVar var = SmtBVVar(iname, rmap.first, rmap.second);
      smod->addPort(var);
      variables.push_back(var.getName());
      smod->addVarDec(SmtBVVarDec(SmtBVVarGetCurr(var)));
      smod->addNextVarDec(SmtBVVarDec(SmtBVVarGetNext(var)));
      smod->addInitVarDec(SmtBVVarDec(SmtBVVarGetInit(var)));
    }
    ASSERT(modMap.count(iref),"DEBUG ME: Missing iref");
    smod->addStmt(modMap[iref]->toInstanceString(inst, imap.first));
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt(";; END module declaration\n");
    }
  }

  smod->addStmt(";; START connections definition");
  for (auto con : def->getConnections()) {
    Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
    Wireable* right = left==con.first ? con.second : con.first;
    SmtBVVar vleft(left);
    SmtBVVar vright(right);

    variables = check_interface_variable(variables, vleft, smod);
    variables = check_interface_variable(variables, vright, smod);
    
    smod->addStmt(SMTAssign(vleft, vright));
  }
  smod->addStmt(";; END connections definition\n");

  return false;
}

void Passes::SmtLib2::writeToStream(std::ostream& os) {

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
