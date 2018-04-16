#include "coreir/simulator/subcircuit.h"

#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
#include "coreir/passes/transform/deletedeadinstances.h"
#include "coreir/passes/transform/fold_constants.h"
#include "coreir/simulator/algorithm.h"
#include "coreir/simulator/op_graph.h"
#include "coreir/simulator/wiring_utils.h"
#include "coreir/simulator/utils.h"

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

  bool hasInputFrom(CoreIR::Instance* const inst,
                    const std::set<Wireable*>& alreadyDetermined,
                    std::map<Wireable*, Wireable*>& driverMap) {
    //cout << "Checking determination of " << inst->toString() << endl;

    for (Select* sel : allInputSelects(inst)) {

      if (contains_key(cast<Wireable>(sel), driverMap) && 
          elem(extractSource(cast<Select>(driverMap[sel])), alreadyDetermined)) {

        return true;

      }

    }

    return false;

  }
  
  bool inputsAreDeterminedBy(CoreIR::Instance* const inst,
                             const std::set<Wireable*>& alreadyDetermined,
                             std::map<Wireable*, Wireable*>& driverMap) {

    cout << "Checking determination of " << inst->toString() << endl;

    bool allAncestorsDetermined = true;

    for (Select* sel : allInputSelects(inst)) {

      if (contains_key(cast<Wireable>(sel), driverMap) && 
          !elem(extractSource(cast<Select>(driverMap[sel])), alreadyDetermined)) {

        cout << sel->toString() << " is not determined by " << endl;
        for (auto det : alreadyDetermined) {
          cout << "\t" << det->toString() << endl;
        }
        allAncestorsDetermined = false;
        break;
      }

    }

    return allAncestorsDetermined;
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
    
    vector<Instance*> instances;
    for (auto iSel : outSels) {

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
    set<Wireable*> undetermined;
    for (auto portR : def->sel("self")->getSelects()) {
      Wireable* port = portR.second;

      if (!elem(port, determined)) {
        undetermined.insert(port);
      }
    }

    cout << "Determined ports" << endl;
    for (auto det : determined) {
      cout << "\t" << det->toString() << endl;
    }

    cout << "Undetermined ports" << endl;
    for (auto det : undetermined) {
      cout << "\t" << det->toString() << endl;
    }
    
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
    for (auto w : undetermined) {
      concat(toConsider, receiverInstances(w, receiverMap));
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

      if (!elem(cast<Wireable>(next), undetermined) &&
          hasInputFrom(next, undetermined, driverMap)) {
        undetermined.insert(next);

        found = next;
        foundInst = true;

        auto recInstances = receiverInstances(found, receiverMap);
        concat(toConsider, recInstances);

      }

      if (foundInst) {
        assert(found != nullptr);
        notAdded.erase(found);
      }

      if (notAdded.size() % 100 == 0) {
        cout << notAdded.size() << " instances that have not been added" << endl;
      }
    }


    for (auto instR : def->getInstances()) {
      Instance* inst = instR.second;
      if (!elem(cast<Wireable>(inst), undetermined)) {
        subCircuitValues.push_back(inst);
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

    assert(srcModule->hasDef());

    cout << "Creating subcircuit " << moduleName << endl;

    ModuleDef* srcDef = srcModule->getDef();
    Wireable* srcSelf = srcDef->sel("self");

    // Check that all selfPorts are off of self
    for (auto port : selfPorts) {
      ASSERT(isa<Select>(port), "All subcircuit ports must be selects");

      Select* sel = cast<Select>(port);
      Wireable* parent = sel->getParent();

      ASSERT(parent == srcSelf, "All subcircuit ports must be selects off of self");
    }

    vector<pair<string, Type*> > fields;
    for (auto port : selfPorts) {
      Select* sel = cast<Select>(port);
      fields.push_back({sel->getSelStr(), sel->getType()->getFlipped()});
    }

    cout << "Created subcircuit type with " << fields.size() << " fields" << endl;

    for (auto inst : instances) {
      if ((getQualifiedOpName(*inst) == "coreir.reg") ||
          (getQualifiedOpName(*inst) == "coreir.reg_arst") ||
          (getQualifiedOpName(*inst) == "corebit.reg")) {

        Type* tp = inst->sel("out")->getType();
        string name = inst->toString() + "_subcircuit_out";

        fields.push_back({name, tp});

        //cout << "\t" << inst->toString() << " : " << inst->getModuleRef()->toString() << endl;
      }
    }

    Type* modType = c->Record(fields);
    Module* subMod = g->newModuleDecl(moduleName, modType);
    ModuleDef* def = subMod->newModuleDef();

    
    for (auto inst : instances) {
      def->addInstance(inst, inst->getInstname());
    }

    for (auto inst : instances) {
      if ((getQualifiedOpName(*inst) == "coreir.reg") ||
          (getQualifiedOpName(*inst) == "coreir.reg_arst") ||
          (getQualifiedOpName(*inst) == "corebit.reg")) {

        string destName = "self." + inst->toString() + "_subcircuit_out";
        string instName = inst->getInstname() + ".out";
        def->connect(destName, instName);
      }
    }

    auto thisDefInstances = def->getInstances();
    for (auto conn : srcDef->getConnections()) {
      Wireable* fst = conn.first;
      Wireable* snd = conn.second;

      Wireable* fstSrc = extractSource(cast<Select>(fst));
      Wireable* sndSrc = extractSource(cast<Select>(snd));

      Wireable* newFst = nullptr;
      Wireable* newSnd = nullptr;

      if (isa<Instance>(fstSrc) &&
          contains_key(fstSrc->toString(), thisDefInstances)) {
        newFst = replaceSelect(fstSrc,
                               thisDefInstances[fstSrc->toString()],
                               fst);
      } else if (isa<Select>(fstSrc)) {

        Select* fstSel = cast<Select>(fstSrc);
        string str = fstSel->getSelStr();

        bool foundField = false;
        for (auto field : subMod->getType()->getRecord()) {
          if (str == field.first) {
            foundField = true;
            break;
          }
        }

        if (foundField) {
          newFst = replaceSelect(fstSrc,
                                 def->sel("self")->sel(fstSel->getSelStr()),
                                 fst);

          //cout << "Found self select " << newFst->toString() << endl;
        }

      }

      if (isa<Instance>(sndSrc) &&
          contains_key(sndSrc->toString(), thisDefInstances)) {

        newSnd = replaceSelect(sndSrc,
                               thisDefInstances[sndSrc->toString()],
                               snd);
      } else if (isa<Select>(sndSrc)) {

        Select* sndSel = cast<Select>(sndSrc);
        string str = sndSel->getSelStr();

        bool foundField = false;
        for (auto field : subMod->getType()->getRecord()) {
          if (str == field.first) {
            foundField = true;
            break;
          }
        }

        if (foundField) {
          newSnd = replaceSelect(sndSrc,
                                 def->sel("self")->sel(sndSel->getSelStr()),
                                 snd);

          //cout << "Found self select " << newSnd->toString() << endl;
        }

      }

      if ((newFst != nullptr) &&
          (newSnd != nullptr)) {
        def->connect(newFst, newSnd);
      }

    }

    cout << "Done with submod definition" << endl;

    subMod->setDef(def);
  }

  void printConnectionInfo(const std::string& sel) {
  }

  void registersToConstants(CoreIR::Module* const mod,
                            std::unordered_map<std::string, BitVec>& regValues) {
    if (!mod->hasDef()) {
      return;
    }

    ModuleDef* def = mod->getDef();
    Context* c = mod->getContext();

    bool found = true;

    while (found) {
      found = false;

      for (auto instR : def->getInstances()) {
        auto inst = instR.second;

        if ((getQualifiedOpName(*inst) == "coreir.reg") ||
            (getQualifiedOpName(*inst) == "coreir.reg_arst")) {

          //cout << "Found register = " << inst->toString() << endl;

          if (contains_key(inst->toString(), regValues)) {

            BitVec value = regValues.find(inst->toString())->second;

            // cout << "Replacing register = " << inst->toString() << endl;
            // cout << "Connected wireables = " << endl;
            // for (auto wb : inst->getConnectedWireables()) {
            //   cout << "\t" << wb->toString() << endl;
            // }

            string cName = inst->toString() + "_const_value";
            Instance* constR =
              def->addInstance(cName,
                               "coreir.const",
                               {{"width", Const::make(c, value.bitLength())}},
                               {{"value", Const::make(c, value)}});

            Instance* instPT = addPassthrough(inst, "_const_to_register_PT");
            def->removeInstance(inst);

            def->connect(constR->sel("out"), instPT->sel("in")->sel("out"));
            inlineInstance(instPT);
            found = true;
            break;
          }
        }
      }
    }
    
  }

  void partiallyEvaluateCircuit(CoreIR::Module* const wholeTopMod,
                                std::unordered_map<std::string, BitVector>& regMap) {
    cout << "Converting " << regMap.size() << " registers to constants" << endl;
    for (auto reg : regMap) {
      cout << "\t" << reg.first << " ---> " << reg.second << endl;
    }

    // cout << "Top module before converting registers to constants" << endl;
    // wholeTopMod->print();
    
    registersToConstants(wholeTopMod, regMap);

    // cout << "Instances converting registers to constants" << endl;
    // for (auto inst : wholeTopMod->getDef()->getInstances()) {
    //   cout << "\t" << inst.second->toString() << " : " << inst.second->getModuleRef()->toString() << endl;

    //   if (getQualifiedOpName(*(inst.second)) == "coreir.const") {
    //     BitVec value = inst.second->getModArgs().at("value")->get<BitVec>();
    //     cout << "\tValue = " << value << endl;
    //   }

    //   if (getQualifiedOpName(*(inst.second)) == "corebit.const") {
    //     bool value = inst.second->getModArgs().at("value")->get<bool>();
    //     cout << "\tValue = " << value << endl;
    //   }

    // }

    // cout << "Top module after converting registers to constants" << endl;
    // wholeTopMod->print();

    cout << wholeTopMod->toString() << endl;
    if (!saveToFile(wholeTopMod->getContext()->getGlobal(), "sb_unq1_registered.json", wholeTopMod)) {
      cout << "Could not save to json!!" << endl;
      assert(false);
    }
  
    cout << "Deleting dead instances" << endl;
    deleteDeadInstances(wholeTopMod);

    cout << "# of instances partially evaluated top after deleting dead instances = " << wholeTopMod->getDef()->getInstances().size() << endl;

    cout << "Folding constants to finish partial evaluation" << endl;
    foldConstants(wholeTopMod);

    cout << "Done folding constants" << endl;

    deleteDeadInstances(wholeTopMod);

    cout << "# of instances partially evaluated top after constant folding = " << wholeTopMod->getDef()->getInstances().size() << endl;

  }


  Module* createSubCircuit(CoreIR::Module* const topMod,
                           std::vector<CoreIR::Wireable*>& subCircuitPorts,
                           std::vector<CoreIR::Instance*>& subCircuitInstances,
                           CoreIR::Context* const c) {
  
    // Create the subcircuit for the config, this could be isolated into a function
    addSubcircuitModule("topMod_config",
                        topMod,
                        subCircuitPorts,
                        subCircuitInstances,
                        c,
                        c->getGlobal());

    Module* topMod_conf =
      c->getGlobal()->getModule("topMod_config");

    assert(topMod_conf != nullptr);
    assert(topMod_conf->hasDef());

    deleteDeadInstances(topMod_conf);

    cout << "# of instances in subcircuit after deleting dead instances = " << topMod_conf->getDef()->getInstances().size() << endl;

    c->setTop(topMod_conf);
    c->runPasses({"removeconstduplicates"});

    cout << "# of instances in subcircuit after deleting duplicate constants = " << topMod_conf->getDef()->getInstances().size() << endl;
  
    cout << "Saving the config circuit" << endl;
    if (!saveToFile(c->getGlobal(), "topModConfig.json", topMod_conf)) {
      cout << "Could not save to json!!" << endl;
      c->die();
    }

    return topMod_conf;
  }
  
}
