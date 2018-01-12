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

  bool hasInputFrom(CoreIR::Instance* const inst,
                    const std::set<Wireable*>& alreadyDetermined,
                    std::map<Wireable*, Wireable*>& driverMap) {
    //cout << "Checking determination of " << inst->toString() << endl;

    for (Select* sel : allInputSelects(inst)) {

      if (contains_key(cast<Wireable>(sel), driverMap) && 
          elem(extractSource(cast<Select>(driverMap[sel])), alreadyDetermined)) {

        return true;

        // cout << sel->toString() << " is not determined by " << endl;
        // for (auto det : alreadyDetermined) {
        //   cout << "\t" << det->toString() << endl;
        // }
        // allAncestorsDetermined = false;
        // break;
      }

    }

    return false;
    //return allAncestorsDetermined;

  }
  
  bool inputsAreDeterminedBy(CoreIR::Instance* const inst,
                             const std::set<Wireable*>& alreadyDetermined,
                             std::map<Wireable*, Wireable*>& driverMap) {

    cout << "Checking determination of " << inst->toString() << endl;

    bool allAncestorsDetermined = true;

    for (Select* sel : allInputSelects(inst)) {
      //bool foundAncestor = false;

      // if (!((!contains_key(cast<Wireable>(sel), driverMap)) ||
      //       elem(extractSource(cast<Select>(driverMap[sel])), alreadyDetermined))) {
        //isAncestorOf(w, driverMap[sel])) {

        //foundAncestor = true;

      if (contains_key(cast<Wireable>(sel), driverMap) && 
          !elem(extractSource(cast<Select>(driverMap[sel])), alreadyDetermined)) {

        cout << sel->toString() << " is not determined by " << endl;
        for (auto det : alreadyDetermined) {
          cout << "\t" << det->toString() << endl;
        }
        allAncestorsDetermined = false;
        break;
      }

      // if (foundAncestor == false) {
      //   return false;
      // }
    }

    return allAncestorsDetermined;

    // cout << inst->toString() << endl;

    // return true;
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

    // cout << "Instances to consider" << endl;
    // for (auto inst : toConsider) {
    //   cout << "\t" << inst->toString() << endl;
    // }

    // Need to add all constants

    // cout << "Adding all constants (and other zero input nodes)" << endl;
    // for (auto instS : def->getInstances()) {
    //   Instance* inst = instS.second;

    //   if (inputsAreDeterminedBy(inst, determined, driverMap) &&
    //       !elem(inst, alreadyAdded)) {

    //     determined.insert(inst);
    //     //subCircuitValues.push_back(inst);
    //     alreadyAdded.insert(inst);

    //     concat(toConsider, receiverInstances(inst, receiverMap));
    //   }
      
    // }

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

      // if (inputsAreDeterminedBy(next, determined, driverMap) &&
      //     !elem(next, alreadyAdded)) {

      if (!elem(cast<Wireable>(next), undetermined) &&
          hasInputFrom(next, undetermined, driverMap)) {
        undetermined.insert(next);
        //subCircuitValues.push_back(next);
        //alreadyAdded.insert(next);

        found = next;
        foundInst = true;

        auto recInstances = receiverInstances(found, receiverMap);
        // cout << found->toString() << " has receiver instances" << endl;
        // for (auto inst : recInstances) {
        //   cout << "\t" << inst->toString() << endl;
        // }

        concat(toConsider, recInstances);

        //cout << "Instance " << next->toString() << " : " << next->getModuleRef()->toString() << " is determined by the existing subcircuit" << endl;

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


    for (auto instR : def->getInstances()) {
      Instance* inst = instR.second;
      if (!elem(cast<Wireable>(inst), undetermined)) {
        subCircuitValues.push_back(inst);
      }
    }

    // Verify the result
    // cout << "Checking that all needed instances have been added" << endl;
    // for (auto instS : def->getInstances()) {
    //   Instance* inst = instS.second;

    //   if (inputsAreDeterminedBy(inst, determined, driverMap) &&
    //       !elem(inst, alreadyAdded)) {

    //     determined.insert(inst);
    //     subCircuitValues.push_back(inst);
    //     alreadyAdded.insert(inst);

    //     cout << "Instance " << inst->toString() << " : " << inst->getModuleRef()->toString() << "\n\tis determined by the config ports, but wasnt added" << endl;

    //     assert(false);
    //   }
      
    // }

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

    for (auto inst : instances) {
      if ((getQualifiedOpName(*inst) == "coreir.reg") ||
          (getQualifiedOpName(*inst) == "coreir.regrst") ||
          (getQualifiedOpName(*inst) == "corebit.dff")) {

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
          (getQualifiedOpName(*inst) == "coreir.regrst") ||
          (getQualifiedOpName(*inst) == "corebit.dff")) {

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

    subMod->setDef(def);
  }

  bool foldConstants(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return false;
    }

    ModuleDef* def = mod->getDef();
    //Context* c = mod->getContext();

    auto driverMap = signalDriverMap(def);
    auto receiverMap = signalReceiverMap(def);

    for (auto instR : def->getInstances()) {
      if (getQualifiedOpName(*(instR.second)) == "coreir.const") {
        Instance* inst = instR.second;
        cout << "Found constant to fold = " << inst->toString() << endl;

        vector<Select*> receivers =
          getReceiverSelects(inst);

        cout << "Connections" << endl;
        for (auto sel : receivers) {
          cout << "\tConnects to " << sel->toString() << endl;
        }
      } else if (getQualifiedOpName(*(instR.second)) == "coreir.mux") {
        Instance* inst = instR.second;

        cout << "Found mux " << inst->toString() << endl;
        auto wbs = inst->sel("sel")->getConnectedWireables();

        assert(wbs.size() == 1);

        Wireable* ptr = *std::begin(wbs);

        cout << "Conneted to " << ptr->toString() << endl;

        assert(isa<Select>(ptr));

        Wireable* src = extractSource(cast<Select>(ptr));

        if (isa<Instance>(src) &&
            (getQualifiedOpName(*(cast<Instance>(src))) == "coreir.const")) {

          Instance* srcConst = cast<Instance>(src);
          //cout << "Found constant mux" << endl;

          BitVec val =
            (srcConst->getModArgs().find("value"))->second->get<BitVec>();

          //cout << "value = " << val << endl;

          Select* bitSelect = cast<Select>(ptr);

          string selStr = bitSelect->getSelStr();
          Wireable* parent = cast<Select>(bitSelect->getParent())->getParent();

          // cout << "Parent = " << parent->toString() << endl;
          // cout << "Src    = " << src->toString() << endl;
          assert(parent == src);
          assert(isNumber(selStr));

          int offset = stoi(selStr);

          uint8_t bit = val.get(offset);

          assert((bit == 0) || (bit == 1));

          Select* replacement = nullptr;
          Select* toReplace = inst->sel("out");
          if (bit == 0) {
            replacement = inst->sel("in0");
          } else {
            assert(bit == 1);
            replacement = inst->sel("in1");
          }

          //cout << "Receivers of mux output to rewire" << endl;
          for (auto sel : drivenBy(toReplace, receiverMap)) {
            //cout << "\t" << "sel = " << sel->toString() << endl;

            auto target = driverMap[sel];

            //cout << "\tsel driver = " << target->toString() << endl;

            Select* val =
              cast<Select>(replaceSelect(toReplace,
                                         replacement,
                                         cast<Select>(target)));

            //cout << "replacement select = " << val->toString() << endl;

            auto driver = map_find(cast<Wireable>(val), driverMap);
            // Select* driver = nullptr;
            assert(driver != nullptr);

            //cout << "replacement select driven by " << driver->toString() << endl;

            //cout << "connecting " << sel->toString() << " <--> " << driver->toString() << endl;
            def->connect(sel, driver);
          }

          assert(replacement != nullptr);

          def->removeInstance(inst);

        }
            
      }
    }
    return true;
  }
  
  void registersToConstants(CoreIR::Module* const mod,
                            std::unordered_map<std::string, BitVec>& regValues) {
    if (!mod->hasDef()) {
      return;
    }

    ModuleDef* def = mod->getDef();
    Context* c = mod->getContext();
    for (auto instR : def->getInstances()) {
      auto inst = instR.second;
      if (getQualifiedOpName(*inst) == "coreir.reg") {

        cout << "Found register = " << inst->toString() << endl;

        if (contains_key(inst->toString(), regValues)) {

          BitVec value = regValues.find(inst->toString())->second;

          cout << "Replacing register = " << inst->toString() << endl;
          cout << "Connected wireables = " << endl;
          for (auto wb : inst->getConnectedWireables()) {
            cout << "\t" << wb->toString() << endl;
          }

          string cName = inst->toString() + "_const_value";
          Instance* constR =
            def->addInstance(cName,
                             "coreir.const",
                             {{"width", Const::make(c, value.bitLength())}},
                             {{"value", Const::make(c, value)}});

          Select* regOutSel = cast<Select>(inst->sel("out"));
          Select* constOutSel = cast<Select>(constR->sel("out"));

          for (auto& conn : def->getConnections()) {
            Wireable* connFst = replaceSelect(regOutSel, constOutSel, conn.first);
            Wireable* connSnd = replaceSelect(regOutSel, constOutSel, conn.second);

            def->disconnect(conn.first, conn.second);
            def->connect(connFst, connSnd);
            
          }

          def->removeInstance(inst);
        }
      }
    }
  }

}
