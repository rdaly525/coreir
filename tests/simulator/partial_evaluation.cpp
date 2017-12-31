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

          
          string cName = inst->toString() + "_const_value";
          Instance* constR =
            def->addInstance(cName,
                             "coreir.const",
                             {{"width", Const::make(c, value.bitLength())}},
                             {{"value", Const::make(c, value)}});

          // How to find what the register is connected to?
          //def->connect(constR->sel("out"), );

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

      // PartialEvaluator pe(rg);
      // pe.setValue("self.clk", BitVec(1, 0));
      // pe.eval();

      // pe.setValue("self.clk", BitVec(1, 1));
      // pe.setValue("self.en", BitVec(1, 1));
      // pe.setValue("self.in", BitVec(width, 5));

      // pe.eval();

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

      cout << "Instances after conversion" << endl;
      for (auto inst : rg->getDef()->getInstances()) {
        cout << inst.first << ": " << inst.second->toString() << endl;
      }
    }

    deleteContext(c);
  }
}
