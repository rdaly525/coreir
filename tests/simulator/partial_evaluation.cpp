#include "catch.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/passes/transform/deletedeadinstances.h"
#include "coreir/passes/transform/unpackconnections.h"

#include "coreir/simulator/output.h"
#include "coreir/simulator/simulator.h"
#include "coreir/simulator/utils.h"
#include "coreir/simulator/wiring_utils.h"

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  class PartialEvaluator {
    CoreIR::Module* mod;

    CircuitState last;
    CircuitState current;

    std::set<SimValue*> allocatedValues;

  public:
    PartialEvaluator(Module* const mod_) : mod(mod_) {}

    SimBitVector* makeSimBitVector(const BitVector& bv) {
      auto sbv  = new SimBitVector(bv);
      allocatedValues.insert(sbv);

      return sbv;
    }
    
    void setValue(const std::string& name,
                  const BitVec& bv) {
      ModuleDef* def = mod->getDef();
      Wireable* w = def->sel(name);
      Select* s = toSelect(w);

      setValue(s, bv);
    }

    void setValue(CoreIR::Select* const sel,
                  const BitVec& bv) {
      setValue(sel, makeSimBitVector(bv));
    }

    SimValue* getValue(CoreIR::Select* sel) {
      if (arrayAccess(sel)) {

        SimBitVector* val =
          static_cast<SimBitVector*>(getValue(toSelect(sel->getParent())));

        assert(val != nullptr);

        int index = selectNum(sel);

        return makeSimBitVector(BitVec(1, (val->getBits()).get(index)));
      }

      assert(mod->getDef()->hasSel(sel->toString()));

      auto it = current.valMap.find(sel);

      if (it == std::end(current.valMap)) {
        return nullptr;
      }

      return (*it).second;
    }

    bool valMapContains(CoreIR::Select* sel) const {
      return current.valMap.find(sel) != std::end(current.valMap);
    }
    
    bool isSet(const std::string& selStr) const {
      Select* s = findSelect(selStr);

      return isSet(s);
    }

    bool isSet(CoreIR::Select* s) const {
      if (!valMapContains(s)) {

        string str = s->getSelStr();
        if (isNumber(str)) {
          return isSet(toSelect(s->getParent()));
        }

        return false;
      }

      return true;
    }
    
    CoreIR::Select* findSelect(const std::string& name) const {
      ModuleDef* def = mod->getDef();
      Wireable* w = def->sel(name);
      Select* s = toSelect(w);

      return s;
    }
    
    void setValue(CoreIR::Select* const sel,
                  SimValue* val) {

      if (arrayAccess(sel)) {

        assert(val->getType() == SIM_VALUE_BV);

        SimBitVector* bv = static_cast<SimBitVector*>(val);
        BitVector bits = bv->getBits();

        assert(bits.bitLength() == 1);
      
        Select* parent = toSelect(sel->getParent());
        int arrLen = arrayLen(parent);

        SimBitVector* val;
        if (isSet(parent)) {
          val = static_cast<SimBitVector*>(getValue(parent));
        } else {
          // TODO: Wrap allocations and delete at end of context
          val = makeSimBitVector(BitVector(arrLen));
        }

        BitVector oldBv = val->getBits();

        int index = selectNum(sel);
        oldBv.set(index, bits.get(0));

        current.valMap[parent] = makeSimBitVector(oldBv);

      }

      current.valMap[sel] = val;
    }

    void incrementTime() {
      last = current;
      current = {};
    }
    
    void eval() {

      // Update comb logic
      // Update clocks
      // Update comb logic again
      
      last = current;

    }

    ~PartialEvaluator() {
      for (auto val : allocatedValues) {
        delete val;
      }
    }
  };

  bool foldConstants(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return false;
    }

    ModuleDef* def = mod->getDef();
    Context* c = mod->getContext();

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

  TEST_CASE("Partial evaluation") {
    Context* c = newContext();

    SECTION("Partially evaluate a mux whose select is a register") {

      uint width = 8;
      Type* combLoop =
        c->Record({{"clk", c->Named("coreir.clkIn")},
              {"regIn", c->BitIn()->Arr(1)},
              {"in0", c->BitIn()->Arr(width)},
                {"in1", c->BitIn()->Arr(width)},
                  {"out", c->Bit()->Arr(width)}});

      Module* cl = c->getGlobal()->newModuleDecl("cl", combLoop);
      ModuleDef* def = cl->newModuleDef();

      def->addInstance("r", "coreir.reg", {{"width", Const::make(c, 1)}});
      def->addInstance("mux0", "coreir.mux", {{"width", Const::make(c, width)}});

      def->connect("self.regIn", "r.in");
      def->connect("self.clk", "r.clk");
      def->connect("r.out.0", "mux0.sel");

      def->connect("self.in0", "mux0.in0");
      def->connect("self.in1", "mux0.in1");

      def->connect("mux0.out", "self.out");

      cl->setDef(def);

      c->runPasses({"rungenerators", "flattentypes", "flatten"});

      SimulatorState state(cl);
      state.setClock("self.clk", 0, 1);
      state.setValue("self.regIn", BitVec(1, 1));
      state.setValue("self.in0", BitVec(width, 56));
      state.setValue("self.in1", BitVec(width, 12));

      state.execute();
      state.execute();
      
      REQUIRE(state.getBitVec("self.out") == BitVec(width, 12));

      CircuitState st = state.getCircStates().back();

      cout << "RMux Instances before conversion" << endl;
      for (auto inst : cl->getDef()->getInstances()) {
        cout << inst.first << ": " << inst.second->toString() << endl;
      }

      registersToConstants(cl, st.registers);
      deleteDeadInstances(cl);
      unpackConnections(cl);
      foldConstants(cl);

      // cout << "RMux Instances after conversion" << endl;
      // for (auto inst : cl->getDef()->getInstances()) {
      //   cout << inst.first << ": " << inst.second->toString() << endl;
      // }

      // auto sigDrivers = signalDriverMap(cl->getDef());
      // cout << "Signal bits to drivers" << endl;
      // for (auto dp : sigDrivers) {
      //   cout << "\t" << dp.first->toString() << " driven by " << dp.second->toString() << endl;
      // }

      // auto sigReceivers = signalReceiverMap(cl->getDef());
      // cout << "Signal bits to receivers" << endl;
      // for (auto dp : sigReceivers) {
      //   cout << "\t" << dp.first->toString() << " drives ";
      //   for (auto val : dp.second) {
      //     cout << val->toString() << ", " << endl;
      //   }
      // }
      
      SECTION("The mux is removed by constant folding") {
        REQUIRE(cl->getDef()->getInstances().size() == 1);

        bool foundMux = false;
        for (auto& inst : cl->getDef()->getInstances()) {
          if (getQualifiedOpName(*(inst.second)) == "coreir.mux") {
            foundMux = true;
            break;
          }
        }

        REQUIRE(!foundMux);

      }

      SECTION("The circuit output is in1") {

        cout << "RMux Connections" << endl;
        for (auto& conn : cl->getDef()->getConnections()) {
          cout << "\t" << conn.first->toString() << " <---> " << conn.second->toString() << endl;
        }

        SimulatorState state2(cl);
        state2.setValue("self.in0", BitVec(width, 8));
        state2.setValue("self.in1", BitVec(width, 4));
        state2.setValue("self.regIn", BitVec(width, 0));
        state2.setClock("self.clk", 0, 1);

        state2.execute();
        state2.execute();

        REQUIRE(state2.getBitVec("self.out") == BitVec(width, 4));
      }

    }

    SECTION("Partially evaluating a register") {
      uint width = 16;

      Type* regOut =
        c->Record({{"clk", c->Named("coreir.clkIn")},
              {"in", c->BitIn()->Arr(width)},
                {"en", c->BitIn()},
                {"out", c->Bit()->Arr(width)}});

      Module* rg = c->getGlobal()->newModuleDecl("rg", regOut);
      ModuleDef* def = rg->newModuleDef();

      def->addInstance("r", "mantle.reg", {{"width", Const::make(c, width)}, {"has_en", Const::make(c, true)}});

      def->connect("self.en", "r.en");
      def->connect("self.clk", "r.clk");
      def->connect("self.in", "r.in");
      def->connect("r.out", "self.out");

      rg->setDef(def);

      c->runPasses({"rungenerators", "flattentypes", "flatten"});

      SimulatorState state(rg);
      state.setClock("self.clk", 0, 1);
      state.setValue("self.en", BitVec(1, 1));
      state.setValue("self.in", BitVec(width, 56));

      state.execute();
      state.execute();
      
      REQUIRE(state.getBitVec("self.out") == BitVec(width, 56));

      CircuitState st = state.getCircStates().back();

      for (auto inst : rg->getDef()->getInstances()) {
        cout << inst.first << ": " << inst.second->toString() << endl;
      }

      registersToConstants(rg, st.registers);
      deleteDeadInstances(rg);

      for (auto inst : rg->getDef()->getInstances()) {
        cout << inst.first << ": " << inst.second->toString() << endl;
      }

      for (auto& conn : rg->getDef()->getConnections()) {
        cout << conn.first->toString() << " <---> " << conn.second->toString() << endl;
      }
    }

    deleteContext(c);
  }
}
