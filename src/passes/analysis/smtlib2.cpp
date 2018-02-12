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

  Module* m = node.getModule();
  SMTModule* smod = new SMTModule(m);
  modMap[m] = smod;

  // There will be plenty of extraneous modules that don't make it past here
  if (!m->hasDef()) {
    return false;
  }

  ModuleDef* def = m->getDef();

  // There will likely be modules that don't have any instances in the design
  static std::vector<string> variables;
  for (auto imap : def->getInstances()) {
    string iname = imap.first;
    Instance* inst = imap.second;
    Module* mref = imap.second->getModuleRef();
    // do not add comment for no ops
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt(";; START module declaration for instance '" + imap.first + "' (Module "+ mref->getName() + ")");
    }
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      SmtBVVar var = SmtBVVar(iname, rmap.first, rmap.second);
      smod->instantiate();
      smod->addPort(var);
      variables.push_back(var.getName());
      smod->addVarDec(SmtBVVarDec(SmtBVVarGetCurr(var)));
      smod->addNextVarDec(SmtBVVarDec(SmtBVVarGetNext(var)));
      smod->addInitVarDec(SmtBVVarDec(SmtBVVarGetInit(var)));
    }
    ASSERT(modMap.count(mref),"DEBUG ME: Missing iref: " + mref->getName());
    smod->addStmt(modMap[mref]->toInstanceString(inst, imap.first));
    if (no_ops.count(imap.first) == 0 ) {
      smod->addStmt(";; END module declaration\n");
    }
  }

  smod->addStmt(";; START connections definition");
  for (auto con : def->getConnections()) {
    Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
    Wireable* right = left==con.first ? con.second : con.first;

    SmtBVVar vleft, vright;

    if (isNumber(left->getSelectPath().back())) {
      auto lsel = dyn_cast<Select>(left)->getParent();
      vleft = SmtBVVar(lsel);
    } else {
      vleft = SmtBVVar(left);
    }

    if (isNumber(right->getSelectPath().back())) {
      auto rsel = dyn_cast<Select>(right)->getParent();
      vright = SmtBVVar(rsel);
    } else {
      vright = SmtBVVar(right);
    }

    variables = check_interface_variable(variables, vleft, smod);
    variables = check_interface_variable(variables, vright, smod);

    SmtBVVar lleft(left);
    SmtBVVar lright(right);

    smod->addStmt(SMTAssign(lleft, lright));
  }
  smod->addStmt(";; END connections definition\n");

  return false;
}

void Passes::SmtLib2::writeToStream(std::ostream& os) {

  os << "(set-logic QF_BV)" << endl;

  os << ";; Init Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0 && mmap.second->isInstantiated()) {
      os << mmap.second->toInitVarDecString() << endl;
    }
  }

  os << ";; Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0  && mmap.second->isInstantiated()) {
      os << mmap.second->toVarDecString() << endl;
    }
  }

  os << ";; Next Variable declarations" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0 && mmap.second->isInstantiated()) {
      os << mmap.second->toNextVarDecString() << endl;
    }
  }

  os << ";; Modules definitions" << endl;
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0 && mmap.second->isInstantiated()) {
      os << mmap.second->toString() << endl;
    }
  }


}
