#include "coreir/passes/transform/deletedeadinstances.h"

std::string CoreIR::Passes::DeleteDeadInstances::ID = "deletedeadinstances";

using namespace std;

namespace CoreIR {


  bool hasOutputConnection(Wireable* w) {
    for (auto wb : w->getConnectedWireables()) {
      if ((wb->getType()->getDir() == Type::DK_In) ||
          (wb->getType()->getDir() == Type::DK_InOut)) {
        return true;
      }
    }

    for (auto smap : w->getSelects()) {
      if (hasOutputConnection(smap.second)) {
        return true;
      }
    }
    return false;
  }
  
  bool deleteDeadInstances(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return false;
    }

    ModuleDef* def = mod->getDef();

    bool changed = false;
    
    do {
      changed = false;
      vector<Instance*> toDelete;
      for (auto instR : def->getInstances()) {
        Instance* inst = instR.second;
        if (!hasOutputConnection(inst)) {
          changed = true;
          toDelete.push_back(inst);
        }
      }
      for (auto inst : toDelete) {
        def->removeInstance(inst);
      }

    } while (changed);

    return changed;
  }



  namespace Passes {

    bool DeleteDeadInstances::runOnModule(Module* m) {
      return deleteDeadInstances(m);
    }
  }
}
