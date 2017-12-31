#include "catch.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"

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
  
  void deleteDeadInstances(CoreIR::Module* const mod) {
    if (!mod->hasDef()) {
      return;
    }

    ModuleDef* def = mod->getDef();

    bool changed = true;

    while (changed) {
      changed = false;

      for (auto instR : def->getInstances()) {
        Instance* inst = instR.second;

        if (!hasOutputConnection(inst)) {
          changed = true;
          def->removeInstance(inst);
        }
      }
    }
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

          // How to find what the register output is connected to?
          //def->connect(constR->sel("out"), );
          for (auto& conn : def->getConnections()) {
            if (conn.first == inst->sel("out")) {
              def->connect(constR->sel("out"), conn.second);
            } else if (conn.second == inst->sel("out")) {
              def->connect(conn.second, constR->sel("out"));
            }
          }

          def->removeInstance(inst);
        }
      }
    }
  }

  TEST_CASE("Partial evaluation") {
    Context* c = newContext();

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
