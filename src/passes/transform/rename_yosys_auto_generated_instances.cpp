#include "coreir/passes/transform/rename_yosys_auto_generated_instances.h"

#include "coreir.h"

using namespace std;
using namespace CoreIR;


bool Passes::RenameYosysAutoGeneratedInstances::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  bool renamedSomething = false;
  int ind = 0;

  string autoGenPrefix = "__DOLLAR__";
  ModuleDef* def = m->getDef();
  set<Instance*> toRemove;

  for (auto instM : def->getInstances()) {
    Instance* inst = instM.second;

    if (inst->toString().substr(0, autoGenPrefix.size()) == autoGenPrefix) {

      toRemove.insert(inst);
      renamedSomething = true;

    }
  }

  for (auto inst : toRemove) {
      
    //cout << "Replacing weirdly named instance " << inst->toString() << endl;

    Instance* instPt = addPassthrough(inst, "_rename_yosys_pt");

    Instance* instCpy = def->addInstance(inst, inst->getModuleRef()->getLongName() + "_" + to_string(ind));
    ind++;
      
    def->disconnect(instPt->sel("in"));
    def->connect(instPt->sel("in"), instCpy);

    def->removeInstance(inst);
    inlineInstance(instPt);
  }

  cout << "Done renaming" << endl;

  return renamedSomething;
}
