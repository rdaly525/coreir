#include "coreir/simulator/subcircuit.h"

#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/wiring_utils.h"

using namespace std;

namespace CoreIR {

  std::vector<Select*>
  allInputSelects(CoreIR::Wireable* inst) {
    vector<Select*> conns;

    for (auto sel : inst->getSelects()) {
      if (sel.second->getType()->getDir() == Type::DK_In) {
        conns.push_back(cast<Select>(sel.second));
      }
    }

    for (auto sel : inst->getSelects()) {
      concat(conns, allInputSelects(sel.second));
    }

    return conns;
  }
  
  bool inputsAreDeterminedBy(CoreIR::Instance* const inst,
                             const std::vector<Wireable*>& alreadyDetermined,
                             std::map<Wireable*, Wireable*>& driverMap) {
    for (Select* sel : allInputSelects(inst)) {
      bool foundAncestor = false;

      for (auto w : alreadyDetermined) {
        if ((!contains_key(cast<Wireable>(sel), driverMap)) || isAncestorOf(w, driverMap[sel])) {
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

    cout << "Building driver map" << endl;
    map<Wireable*, Wireable*> driverMap = signalDriverMap(def);
    cout << "Done building driver map" << endl;

    bool foundInst = true;
    while (foundInst) {
      foundInst = false;

      for (auto inst : def->getInstances()) {

        if (inputsAreDeterminedBy(inst.second, determined, driverMap) &&
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
