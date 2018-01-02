#include "catch.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/passes/transform/deletedeadinstances.h"

#include "coreir/simulator/output.h"
#include "coreir/simulator/simulator.h"
#include "coreir/simulator/utils.h"

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  class PartialEvaluator {
    CoreIR::Module* mod;

    CircuitState last;
    CircuitState current;

  public:
    PartialEvaluator(Module* const mod_) : mod(mod_) {}

    void setValue(const std::string& name,
                  const BitVec& bv) {
      ModuleDef* def = mod->getDef();
      Wireable* w = def->sel(name);
      Select* s = toSelect(w);

      setValue(s, bv);
    }

    void setValue(CoreIR::Select* const sel,
                  const BitVec& bv) {
    }
    
    void eval() {

      // Update comb logic
      // Update clocks
      // Update comb logic again
      
      last = current;
    }
  };

  CoreIR::Wireable* replaceSelect(CoreIR::Wireable* const toReplace,
                                  CoreIR::Wireable* const replacement,
                                  CoreIR::Wireable* const sel) {
    if (toReplace == sel) {
      return replacement;
    }

    if (isa<Select>(sel)) {
      Select* selP = cast<Select>(sel);
      return replaceSelect(toReplace,
                           replacement,
                           selP->getParent())->sel(selP->getSelStr());
    }

    return sel;
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

          // How to find what the register output is connected to?
          //def->connect(constR->sel("out"), );
          for (auto& conn : def->getConnections()) {
            Wireable* connFst = replaceSelect(regOutSel, constOutSel, conn.first);
            Wireable* connSnd = replaceSelect(regOutSel, constOutSel, conn.second);

            def->disconnect(conn.first, conn.second);
            def->connect(connFst, connSnd);
            
            // if (conn.first == inst->sel("out")) {
            //   def->connect(constR->sel("out"), conn.second);
            // } else if (conn.second == inst->sel("out")) {
            //   def->connect(conn.second, constR->sel("out"));
            // }

            // assert(connFst != nullptr);
            // assert(connSnd != nullptr);
            
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

      cout << "RMux Instances after conversion" << endl;
      for (auto inst : cl->getDef()->getInstances()) {
        cout << inst.first << ": " << inst.second->toString() << endl;
      }

      // After conversion there is a mux and a constant for the register
      REQUIRE(cl->getDef()->getInstances().size() == 2);

      for (auto& conn : cl->getDef()->getConnections()) {
        cout << conn.first->toString() << " <---> " << conn.second->toString() << endl;
      }

      SimulatorState state2(cl);
      state2.setValue("self.in1", BitVec(width, 4));
      state2.setClock("self.clk", 0, 1);

      state2.execute();
      state2.execute();

      REQUIRE(state2.getBitVec("self.in1") == BitVec(width, 4));
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

      cout << "Instances before conversion" << endl;
      for (auto inst : rg->getDef()->getInstances()) {
        cout << inst.first << ": " << inst.second->toString() << endl;
      }

      registersToConstants(rg, st.registers);
      deleteDeadInstances(rg);

      cout << "Instances after conversion" << endl;
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
