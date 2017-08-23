#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include "coreir-passes/analysis/smtoperators.hpp"
#include "coreir-passes/analysis/smtlib2.h"

using namespace CoreIR;
using namespace Passes;

namespace {
string SmtBVVarDec(SmtBVVar w) { return "(declare-fun " + w.getName() + " () (_ BitVec " + w.dimstr() + "))"; }
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
      smod->addVarDec(SmtBVVarDec(SmtBVVar(iname+"_"+rmap.first,rmap.second)));
      smod->addVarDec(SmtBVVarDec(SmtBVVar(SMTgetNext(iname+"_"+rmap.first),rmap.second)));
    }
    ASSERT(modMap.count(iref),"DEBUG ME: Missing iref");
    smod->addStmt(modMap[iref]->toInstanceString(inst));
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt(";; END module declaration\n");
    }
    
  }

  smod->addStmt(";; START connections definition");
  for (auto con : def->getConnections()) {
    smod->addStmt(SMTAssign(con));
  }
  smod->addStmt(";; END connections definition\n");

  return false;
}

void Passes::SmtLib2::writeToStream(std::ostream& os) {

  // Print variable declarations
  os << ";; Variable declarations" << endl;
  for (auto mmap : modMap) {
    os << mmap.second->toVarDecString() << endl;
  }

  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) {
      os << mmap.second->toString() << endl;
    }
  }


}
