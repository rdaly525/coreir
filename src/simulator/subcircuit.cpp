#include "coreir/simulator/subcircuit.h"

#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/op_graph.h"
#include "coreir/simulator/wiring_utils.h"

using namespace std;

namespace CoreIR {

  std::vector<Select*>
  allOutputSelects(CoreIR::Wireable* inst) {
    vector<Select*> conns;

    for (auto sel : inst->getSelects()) {
      if (sel.second->getType()->getDir() == Type::DK_Out) {
        conns.push_back(cast<Select>(sel.second));
      }
    }

    for (auto sel : inst->getSelects()) {
      concat(conns, allOutputSelects(sel.second));
    }

    return conns;

  }
  
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
                             const std::set<Wireable*>& alreadyDetermined,
                             std::map<Wireable*, Wireable*>& driverMap) {
    for (Select* sel : allInputSelects(inst)) {
      bool foundAncestor = false;

      //for (auto w : alreadyDetermined) {
      if ((!contains_key(cast<Wireable>(sel), driverMap)) ||
          elem(extractSource(cast<Select>(driverMap[sel])), alreadyDetermined)) {//isAncestorOf(w, driverMap[sel])) {
        foundAncestor = true;
        break;
      }
      //}

      if (foundAncestor == false) {
        return false;
      }
    }

    return true;
  }

  std::vector<CoreIR::Instance*>
  receiverInstances(CoreIR::Wireable* const w,
                    map<Wireable*, vector<Wireable*> >& receiverMap) {
    vector<Select*> outSels = allOutputSelects(w);

    if (isa<Select>(w)) {
      Select* wSel = cast<Select>(w);
      if (wSel->getType()->getDir() == Type::DK_Out) {
        outSels.push_back(wSel);
      }
    }
    
    //cout << "# of output selects from " << w->toString() << " = " << outSels.size() << endl;

    vector<Instance*> instances;
    for (auto iSel : outSels) {
      //cout << "Out select = " << iSel->toString() << endl;

      for (auto sel : receiverMap[iSel]) {
        Wireable* src = extractSource(cast<Select>(sel));
        if (isa<Instance>(src) && !elem(src, instances)) {
          instances.push_back(cast<Instance>(src));
        }
      }
    }
    return instances;
  }

  std::vector<CoreIR::Instance*>
  extractSubcircuit(CoreIR::Module* mod,
                    const std::vector<Wireable*>& startingPorts) {
    if (!mod->hasDef()) {
      return {};
    }

    ModuleDef* def = mod->getDef();

    vector<Instance*> subCircuitValues;

    set<Wireable*> determined(begin(startingPorts), end(startingPorts));
    set<Instance*> alreadyAdded;

    set<Instance*> notAdded;
    for (auto inst : def->getInstances()) {
      notAdded.insert(inst.second);
    }

    cout << "Total instances to check = " << notAdded.size() << endl;

    cout << "Building driver and receiver maps" << endl;
    map<Wireable*, Wireable*> driverMap = signalDriverMap(def);
    map<Wireable*, vector<Wireable*> > receiverMap = signalReceiverMap(def);
    cout << "Done building driver and receiver maps" << endl;

    vector<Instance*> toConsider;
    for (auto w : determined) {
      concat(toConsider, receiverInstances(w, receiverMap));
    }

    // cout << "Instances to consider" << endl;
    // for (auto inst : toConsider) {
    //   cout << "\t" << inst->toString() << endl;
    // }

    // Need to add all constants

    cout << "Adding all constants (and other zero input nodes)" << endl;
    for (auto instS : def->getInstances()) {
      Instance* inst = instS.second;

      if (inputsAreDeterminedBy(inst, determined, driverMap) &&
          !elem(inst, alreadyAdded)) {

        determined.insert(inst);
        subCircuitValues.push_back(inst);
        alreadyAdded.insert(inst);

        concat(toConsider, receiverInstances(inst, receiverMap));
      }
      
    }

    cout << "Initial determined set" << endl;
    for (auto det : determined) {
      cout << "\t" << det->toString() << endl;
    }
    
    bool foundInst = true;
    while (toConsider.size() > 0) {
      foundInst = false;

      Instance* next = toConsider.back();
      Instance* found = nullptr;
      toConsider.pop_back();

      // cout << "Already added = " << endl;
      // for (auto inst : alreadyAdded) {
      //   cout << "\t" << inst->toString() << endl;
      // }

      if (inputsAreDeterminedBy(next, determined, driverMap) &&
          !elem(next, alreadyAdded)) {

        determined.insert(next);
        subCircuitValues.push_back(next);
        alreadyAdded.insert(next);

        found = next;
        foundInst = true;

        auto recInstances = receiverInstances(found, receiverMap);
        // cout << found->toString() << " has receiver instances" << endl;
        // for (auto inst : recInstances) {
        //   cout << "\t" << inst->toString() << endl;
        // }

        concat(toConsider, recInstances);

        cout << "Instance " << next->toString() << " : " << next->getModuleRef()->toString() << " is determined by the existing subcircuit" << endl;

        //cout << "# of nodes to consider = " << toConsider.size() << endl;
        // for (auto inst : toConsider) {
        //   cout << "\t" << inst->toString() << endl;
        // }
        //break;
      }

      if (foundInst) {
        assert(found != nullptr);
        notAdded.erase(found);
      }

      if (notAdded.size() % 100 == 0) {
        cout << notAdded.size() << " instances that have not been added" << endl;
      }
    }

    cout << "Checking that all needed instances have been added" << endl;
    for (auto instS : def->getInstances()) {
      Instance* inst = instS.second;

      if (inputsAreDeterminedBy(inst, determined, driverMap) &&
          !elem(inst, alreadyAdded)) {

        determined.insert(inst);
        subCircuitValues.push_back(inst);
        alreadyAdded.insert(inst);

        cout << "Instance " << inst->toString() << " : " << inst->getModuleRef()->toString() << "\n\tis determined by the config ports, but wasnt added" << endl;

        assert(false);
      }
      
    }

    return subCircuitValues;
  }

  void
  addSubcircuitModule(const std::string& moduleName,
                      CoreIR::Module* const srcModule,
                      const std::vector<Wireable*>& selfPorts,
                      const std::vector<CoreIR::Instance*>& instances,
                      CoreIR::Context* const c,
                      CoreIR::Namespace* const g) {
    // How do I build a subcircuit? I suppose a subcircuit is the same as
    // the original module, but it:
    //
    // 1. Has ports from selfPorts
    // 2. Deletes connections that connect two wireables not in subcircuit
    //    wireables
    // 3. Replaces connections that connect sequential registers to instances
    //    with connections from registers to new ports

    assert(srcModule->hasDef());

    ModuleDef* srcDef = srcModule->getDef();
    Wireable* srcSelf = srcDef->sel("self");

    // Check that all selfPorts are off of self
    for (auto port : selfPorts) {
      ASSERT(isa<Select>(port), "All subcircuit ports must be selects");

      Select* sel = cast<Select>(port);
      Wireable* parent = sel->getParent();

      ASSERT(parent == srcSelf, "All subcircuit ports must be selects off of self");
    }

    // Create module interface by adding all self ports, and adding
    // ports for all register / dff outputs, at the same time create
    // connections between registers and ports

    // Create module definition by adding all instances
    // and creating map from subcircuit instances to original circuit
    // instances.

    // Add all connections between subcircuit wireables, and then add all connections
    // between registers and their output ports
  }

}
