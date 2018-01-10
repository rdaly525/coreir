#include "coreir/simulator/subcircuit.h"
#include "coreir/ir/moduledef.h"
#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/wiring_utils.h"

using namespace std;

namespace CoreIR {

  bool inputsAreDeterminedBy(CoreIR::Instance* const inst,
                             const std::vector<Wireable*>& alreadyDetermined) {
    for (auto sel : getSourceSelects(inst)) {
      bool foundAncestor = false;

      for (auto w : alreadyDetermined) {
        if (isAncestorOf(w, sel)) {
          foundAncestor = true;
          break;
        }
      }

      if (foundAncestor == false) {
        return false;
      }
    }

    return true;
  }

  std::vector<CoreIR::Instance*>
  extractSubcircuit(CoreIR::Module* mod,
                    const std::vector<Wireable*>& startingPorts) {
    if (!mod->hasDef()) {
      return {};
    }

    ModuleDef* def = mod->getDef();

    vector<Instance*> subCircuitValues;

    vector<Wireable*> determined = startingPorts;

    bool foundInst = true;
    while (foundInst) {
      foundInst = false;

      for (auto inst : def->getInstances()) {

        if (inputsAreDeterminedBy(inst.second, determined) &&
            // Turn into set to optimize?
            !elem(inst.second, subCircuitValues)) {
          determined.push_back(inst.second);
          subCircuitValues.push_back(inst.second);
          foundInst = true;
          cout << "Instance " << inst.second->toString() << " is determined by the config ports" << endl;
          break;
        }
      }
    }

    return subCircuitValues;
  }


}
