#include "coreir/simulator/subcircuit.h"

#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
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

  void printConnectionInfo(const std::string& sel) {
  }

  bool foldConstants(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return false;
    }

    ModuleDef* def = mod->getDef();
    Context* c = mod->getContext();

    // set<Instance*> unchecked;
    // for (auto inst : def->getInstances()) {
    //   unchecked.insert(inst.second);
    // }

    set<Instance*> toConsider;
    for (auto inst : def->getInstances()) {
      if (isConstant(inst.second)) {
        for (auto elem : getReceiverSelects(inst.second)) {
          auto src = extractSource(elem);
          if (isa<Instance>(src)) {
            toConsider.insert(cast<Instance>(src));
          }
        }
      }

    }

    int i = 0;
    while (toConsider.size() > 0) {
      if ((i % 100) == 0) {
        cout << "Folding constants, i = " << i << endl;
      }

      i++;

      // assert(def->hasSel("test_pe$test_pe_comp$__DOLLAR__or__DOLLAR____DOT__/pe_verilog/test_pe_comp_unq1__DOT__sv__COLON__298__DOLLAR__368$op0.in0"));

      // Select* sel = cast<Select>(def->sel("test_pe$test_pe_comp$__DOLLAR__or__DOLLAR____DOT__/pe_verilog/test_pe_comp_unq1__DOT__sv__COLON__298__DOLLAR__368$op0.in0"));

      // cout << "# of connected wireables for " << sel->toString() << " ";
      // cout << sel->getConnectedWireables().size() << endl;
      // for (auto wb : sel->getConnectedWireables()) {
      //   cout << "\t" << wb->toString() << endl;
      // }

      // assert(sel->getConnectedWireables().size() == 1);

      Instance* inst = *std::begin(toConsider);
      toConsider.erase(inst);

      cout << "Considering instance " << inst->toString() << endl;
      // cout << "Module before trying to fold" << endl;
      // mod->print();

      if (getQualifiedOpName(*(inst)) == "coreir.mux") {

        //cout << "Found mux " << inst->toString() << endl;
        auto wbs = inst->sel("sel")->getConnectedWireables();

        if (wbs.size() != 1) {
          cout << inst->sel("sel")->toString() << " selects has " << wbs.size() << " connected wireables" << endl;
          for (auto w : wbs) {
            cout << "\t" << w->toString() << endl;
          }
        }

        assert(wbs.size() == 1);

        Wireable* ptr = *std::begin(wbs);

        //cout << "Conneted to " << ptr->toString() << endl;

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

          assert(parent == src);
          assert(isNumber(selStr));

          int offset = stoi(selStr);

          cout << "\tSource = " << srcConst->toString() << endl;
          cout << "\tOffset = " << offset << endl;

          uint8_t bit = val.get(offset);

          assert((bit == 0) || (bit == 1));

          Select* replacement = nullptr;

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src)) {
              toConsider.insert(cast<Instance>(src));
            }
          }

          Instance* instPT = addPassthrough(inst, "_inline_mux_PT");

          if (bit == 0) {
            replacement = instPT->sel("in")->sel("in0");
          } else {
            assert(bit == 1);
            replacement = instPT->sel("in")->sel("in1");
          }

          def->removeInstance(inst);

          def->connect(replacement,
                       instPT->sel("in")->sel("out"));

          inlineInstance(instPT);
            
          //unchecked.erase(inst);
        } else if (isa<Instance>(src) &&
                   (getQualifiedOpName(*(cast<Instance>(src))) == "corebit.const")) {

          Instance* srcConst = cast<Instance>(src);
          bool valB =
            (srcConst->getModArgs().find("value"))->second->get<bool>();

          BitVector val(1, valB == true ? 1 : 0);
          uint8_t bit = val.get(0);

          assert((bit == 0) || (bit == 1));

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src)) {
              toConsider.insert(cast<Instance>(src));
            }
          }
            
          Instance* instPT = addPassthrough(inst, "_inline_mux_PT");

          Select* replacement = nullptr;
          if (bit == 0) {
            replacement = instPT->sel("in")->sel("in0");
          } else {
            assert(bit == 1);
            replacement = instPT->sel("in")->sel("in1");
          }

          def->removeInstance(inst);

          def->connect(replacement,
                       instPT->sel("in")->sel("out"));

          inlineInstance(instPT);

        }
            
      } else if (getQualifiedOpName(*(inst)) == "coreir.zext") {

        Select* input = inst->sel("in");
        vector<Select*> values = getSignalValues(input);

        maybe<BitVec> sigValue = getSignalBitVec(values);

        if (sigValue.has_value()) {
          BitVec sigVal = sigValue.get_value();

          uint inWidth =
            inst->getModuleRef()->getGenArgs().at("width_in")->get<int>();
          uint outWidth =
            inst->getModuleRef()->getGenArgs().at("width_out")->get<int>();

          assert(inWidth == ((uint) sigVal.bitLength()));

          BitVec res(outWidth, 0);
          for (uint i = 0; i < inWidth; i++) {
            res.set(i, sigVal.get(i));
          }
            
          auto newConst =
            def->addInstance(inst->toString() + "_const_replacement",
                             "coreir.const",
                             {{"width", Const::make(c, outWidth)}},
                             {{"value", Const::make(c, res)}});

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src)) {
              toConsider.insert(cast<Instance>(src));
            }
          }

          Instance* instPT = addPassthrough(inst, "_inline_zext_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);

          //unchecked.erase(inst);
        }
      } else if (getQualifiedOpName(*(inst)) == "coreir.eq") {

        Select* in0 = inst->sel("in0");
        Select* in1 = inst->sel("in1");

        vector<Select*> in0Values = getSignalValues(in0);
        vector<Select*> in1Values = getSignalValues(in1);

        // cout << "in0 values" << endl;
        // for (auto val : in0Values) {
        //   cout << "\t" << val->toString() << endl;
        // }
        // cout << "in1 values" << endl;
        // for (auto val : in1Values) {
        //   cout << "\t" << val->toString() << endl;
        // }

        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);
        maybe<BitVec> sigValue1 = getSignalBitVec(in1Values);

        if (sigValue0.has_value() && sigValue1.has_value()) {

          BitVec sigVal0 = sigValue0.get_value();
          BitVec sigVal1 = sigValue1.get_value();

          BitVec res = BitVec(1, (sigVal0 == sigVal1) ? 1 : 0);

          uint inWidth =
            inst->getModuleRef()->getGenArgs().at("width")->get<int>();

          assert(((uint) sigVal0.bitLength()) == inWidth);
          assert(((uint) sigVal1.bitLength()) == inWidth);
          assert(res.bitLength() == 1);

          bool resVal = res == BitVec(1, 1) ? true : false;

          auto newConst =
            def->addInstance(inst->toString() + "_const_replacement",
                             "corebit.const",
                             {{"value", Const::make(c, resVal)}});

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src)) {
              toConsider.insert(cast<Instance>(src));
            }
          }

          Instance* instPT = addPassthrough(inst, "_inline_eq_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);
            
        }

      } else if (getQualifiedOpName(*(inst)) == "coreir.or") {

        Select* in0 = inst->sel("in0");
        Select* in1 = inst->sel("in1");

        vector<Select*> in0Values = getSignalValues(in0);
        vector<Select*> in1Values = getSignalValues(in1);

        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);
        maybe<BitVec> sigValue1 = getSignalBitVec(in1Values);

        if (sigValue0.has_value() && sigValue1.has_value()) {

          BitVec sigVal0 = sigValue0.get_value();
          BitVec sigVal1 = sigValue1.get_value();

          BitVec res = sigVal0 | sigVal1;

          uint inWidth =
            inst->getModuleRef()->getGenArgs().at("width")->get<int>();

          assert(((uint) sigVal0.bitLength()) == inWidth);
          assert(((uint) sigVal1.bitLength()) == inWidth);
          assert(((uint) res.bitLength()) == inWidth);

          auto newConst =
            def->addInstance(inst->toString() + "_const_replacement",
                             "coreir.const",
                             {{"width", Const::make(c, inWidth)}},
                             {{"value", Const::make(c, res)}});

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src)) {
              toConsider.insert(cast<Instance>(src));
            }
          }

          Instance* instPT = addPassthrough(inst, "_inline_or_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);
            
        }

          
      } else if (getQualifiedOpName(*(inst)) == "coreir.orr") {

        Select* in = inst->sel("in");

        vector<Select*> in0Values = getSignalValues(in);

        // cout << "in0 values" << endl;
        // for (auto val : in0Values) {
        //   cout << "\t" << val->toString() << endl;
        // }

        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);

        if (sigValue0.has_value()) {

          BitVec sigVal0 = sigValue0.get_value();

          BitVec res = BitVec(1, 0);
          for (uint i = 0; i < ((uint) sigVal0.bitLength()); i++) {
            if (sigVal0.get(i) == 1) {
              res = BitVec(1, 1);
              break;
            }
          }

          uint inWidth =
            inst->getModuleRef()->getGenArgs().at("width")->get<int>();

          assert(((uint) sigVal0.bitLength()) == inWidth);
          assert(res.bitLength() == 1);

          bool resVal = res == BitVec(1, 1) ? true : false;

          auto newConst =
            def->addInstance(inst->toString() + "_const_replacement",
                             "corebit.const",
                             {{"value", Const::make(c, resVal)}});

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src)) {
              toConsider.insert(cast<Instance>(src));
            }
          }
            
          Instance* instPT = addPassthrough(inst, "_inline_orr_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);

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

    bool found = true;

    while (found) {
      found = false;

      for (auto instR : def->getInstances()) {
        auto inst = instR.second;

        if (getQualifiedOpName(*inst) == "coreir.reg") {

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

}
