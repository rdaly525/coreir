#include "coreir.h"
#include "coreir/passes/transform/fold_constants.h"

using namespace std;
using namespace CoreIR;

string Passes::FoldConstants::ID = "fold-constants";

namespace CoreIR {
  bool foldConstants(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return false;
    }

    ModuleDef* def = mod->getDef();
    Context* c = mod->getContext();

    set<Instance*> toConsider;
    for (auto inst : def->getInstances()) {
      if (isConstant(inst.second)) {
        for (auto elem : getReceiverSelects(inst.second)) {
          auto src = extractSource(elem);
          if (isa<Instance>(src)) {
            toConsider.insert(cast<Instance>(src));
          }
        }
      } else if (getQualifiedOpName(*(inst.second)) == "coreir.reg") {
        toConsider.insert(inst.second);
      }

    }

    int i = 0;
    while (toConsider.size() > 0) {
      if ((i % 100) == 0) {
        cout << "Folding constants, i = " << i << endl;
      }

      i++;

      // assert(sel->getConnectedWireables().size() == 1);

      Instance* inst = *std::begin(toConsider);
      toConsider.erase(inst);
      auto insts = def->getInstances();
      if (!contains_key(inst->toString(), insts)) {
        continue;
      }

      // cout << "Considering instance " << inst->toString() << endl;
      // cout << "Module before trying to fold" << endl;
      // mod->print();

      // cout << "Checking instances " << inst->toString() << endl;
      // cout << "Instance name = " << getQualifiedOpName(*inst) << endl;
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

          // cout << "\tSource = " << srcConst->toString() << endl;
          // cout << "\tOffset = " << offset << endl;

          if (!val.get(offset).is_binary()) {
            continue;
          }

          uint8_t bit = val.get(offset).binary_value();

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

          if (!val.get(0).is_binary()) {
            continue;
          }
          
          uint8_t bit = val.get(0).binary_value();

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

          // cout << "sigVal0 = " << sigVal0 << endl;
          // cout << "sigVal1 = " << sigVal1 << endl;
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

      } else if (getQualifiedOpName(*(inst)) == "corebit.and") {
        Select* in0 = inst->sel("in0");
        Select* in1 = inst->sel("in1");

        vector<Select*> in0Values = getSignalValues(in0);
        vector<Select*> in1Values = getSignalValues(in1);

        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);
        maybe<BitVec> sigValue1 = getSignalBitVec(in1Values);

        if (sigValue0.has_value() && sigValue1.has_value()) {

          BitVec sigVal0 = sigValue0.get_value();
          BitVec sigVal1 = sigValue1.get_value();

          BitVec res = sigVal0 & sigVal1;
          assert(((int) res.bitLength()) == ((int) 1));

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

          Instance* instPT = addPassthrough(inst, "_inline_or_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);
            
        }
        
      } else if (getQualifiedOpName(*(inst)) == "coreir.and") {

        Select* in0 = inst->sel("in0");
        Select* in1 = inst->sel("in1");

        vector<Select*> in0Values = getSignalValues(in0);
        vector<Select*> in1Values = getSignalValues(in1);

        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);
        maybe<BitVec> sigValue1 = getSignalBitVec(in1Values);

        if (sigValue0.has_value() && sigValue1.has_value()) {

          BitVec sigVal0 = sigValue0.get_value();
          BitVec sigVal1 = sigValue1.get_value();

          BitVec res = sigVal0 & sigVal1;

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
        
      } else if (getQualifiedOpName(*(inst)) == "coreir.not") {
        Select* in = inst->sel("in");

        vector<Select*> in0Values = getSignalValues(in);
        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);

        if (sigValue0.has_value()) {

          BitVec sigVal0 = sigValue0.get_value();

          // TODO: Check for binary values
          BitVec res = ~sigVal0;

          auto newConst =
            def->addInstance(inst->toString() + "_const_replacement",
                             "coreir.const",
                             {{"width", Const::make(c, res.bitLength())}},
                             {{"value", Const::make(c, res)}});

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src)) {
              toConsider.insert(cast<Instance>(src));
            }
          }
            
          Instance* instPT = addPassthrough(inst, "_inline_andr_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);

        }
        
      } else if (getQualifiedOpName(*(inst)) == "coreir.andr") {
        Select* in = inst->sel("in");

        vector<Select*> in0Values = getSignalValues(in);
        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);

        if (sigValue0.has_value()) {

          BitVec sigVal0 = sigValue0.get_value();

          // TODO: Check for binary values
          BitVec res = BitVec(1, 1);
          for (uint i = 0; i < ((uint) sigVal0.bitLength()); i++) {
            if (sigVal0.get(i) == 0) {
              res = BitVec(1, 0);
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
            
          Instance* instPT = addPassthrough(inst, "_inline_andr_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);

        }

      } else if (getQualifiedOpName(*inst) == "coreir.reg_arst") {

        Select* rstSel = inst->sel("arst");
        auto inSels = getSourceSelects(rstSel);

        ASSERT(inSels.size() == 1, "coreir.reg_arst must have one select");

        Wireable* p = inSels[0]->getTopParent();
        if (isa<Instance>(p)) {
          Instance* rstSrcInst = cast<Instance>(p);
          if (getQualifiedOpName(*rstSrcInst) == "coreir.wrap") {
            Select* wrapIn = rstSrcInst->sel("in");
            vector<Select*> in0Values = getSignalValues(wrapIn);
            maybe<BitVec> rstValue = getSignalBitVec(in0Values);

            // If the reset port is set to a constant then we may be able to constant
            // fold
            if (rstValue.has_value()) {
        
              Select* inSel = inst->sel("in");
              Select* outSel = inst->sel("out");

              vector<Select*> inValues = getSignalValues(inSel);

              bool allInsFromOut = true;
              for (auto bitVal : inValues) {
                Wireable* src = extractSource(bitVal);

                if (!isa<Instance>(src) || cast<Instance>(src)->sel("out") != outSel) {
                  allInsFromOut = false;
                }
              }

              if (allInsFromOut) {

                BitVector value = inst->getModArgs().at("init")->get<BitVector>();
                auto newConst =
                  def->addInstance(inst->toString() + "_reg_const_replacement",
                                   "coreir.const",
                                   {{"width", Const::make(c, value.bitLength())}},
                                   {{"value", Const::make(c, BitVector(value))}});

                auto recInstances = getReceiverSelects(inst);
                for (auto elem : recInstances) {
                  auto src = extractSource(elem);
                  if (isa<Instance>(src) && (cast<Instance>(src) != inst)) {
                    toConsider.insert(cast<Instance>(src));
                  }
                }
          
                Instance* instPT = addPassthrough(inst, "_remove_reg_PT");
                Select* replacement = newConst->sel("out");

                def->removeInstance(inst);
                def->connect(replacement,
                             instPT->sel("in")->sel("out"));
                inlineInstance(instPT);
          
              }
            }
          }
        }
      } else if (getQualifiedOpName(*inst) == "coreir.reg") {
        Select* inSel = inst->sel("in");
        Select* outSel = inst->sel("out");

        vector<Select*> inValues = getSignalValues(inSel);

        bool allInsFromOut = true;
        for (auto bitVal : inValues) {
          Wireable* src = extractSource(bitVal);

          if (!isa<Instance>(src) || cast<Instance>(src)->sel("out") != outSel) {
            allInsFromOut = false;
          }
        }

        if (allInsFromOut) {

          BitVector value = inst->getModArgs().at("init")->get<BitVector>();
          auto newConst =
            def->addInstance(inst->toString() + "_reg_const_replacement",
                             "coreir.const",
                             {{"width", Const::make(c, value.bitLength())}},
                             {{"value", Const::make(c, BitVector(value))}});

          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src) && (cast<Instance>(src) != inst)) {
              toConsider.insert(cast<Instance>(src));
            }
          }
          
          Instance* instPT = addPassthrough(inst, "_remove_reg_PT");
          Select* replacement = newConst->sel("out");

          def->removeInstance(inst);
          def->connect(replacement,
                       instPT->sel("in")->sel("out"));
          inlineInstance(instPT);
          
        }
        
      } else if (getQualifiedOpName(*inst) == "coreir.wrap") {
        Select* in = inst->sel("in");

        vector<Select*> in0Values = getSignalValues(in);
        maybe<BitVec> sigValue0 = getSignalBitVec(in0Values);

        if (sigValue0.has_value()) {
          auto recInstances = getReceiverSelects(inst);
          for (auto elem : recInstances) {
            auto src = extractSource(elem);
            if (isa<Instance>(src) && (cast<Instance>(src) != inst)) {
              toConsider.insert(cast<Instance>(src));
            }
          }
        }

      } else if (getQualifiedOpName(*(inst)) == "coreir.orr") {

        Select* in = inst->sel("in");

        vector<Select*> in0Values = getSignalValues(in);
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

      } else {
        cout << "No folding rule for " << getQualifiedOpName(*inst) << endl;
      }
    }

    return true;
  }

  namespace Passes {

    bool Passes::FoldConstants::runOnModule(Module* m) {
      return foldConstants(m);
    }

  }

}
