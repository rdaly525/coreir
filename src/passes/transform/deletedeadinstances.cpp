#include "coreir/passes/transform/deletedeadinstances.h"

namespace CoreIR {


  bool hasOutputConnection(Wireable* w) {
    for (auto wb : w->getConnectedWireables()) {
      if (wb->getType()->getDir() == Type::DK_In) {
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

      for (auto instR : def->getInstances()) {
        Instance* inst = instR.second;

        if (!hasOutputConnection(inst)) {
          changed = true;
          def->removeInstance(inst);
        }
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
