#include "catch.hpp"

#include "coreir.h"
#include "coreir-passes/analysis/pass_sim.h"
#include "coreir/passes/transform/rungenerators.h"

#include "fuzzing.hpp"

#include "../src/simulator/output.hpp"
#include "../src/simulator/sim.hpp"
#include "../src/simulator/interpret.hpp"
#include "../src/simulator/utils.hpp"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  TEST_CASE("Interpret simulator graphs") {

    // New context
    Context* c = newContext();
  
    Namespace* g = c->getGlobal();

    SECTION("And 4") {
      cout << "32 bit and 4" << endl;

      uint n = 32;
  
      Generator* and2 = c->getGenerator("coreir.and");

      // Define And4 Module
      Type* and4Type = c->Record({
	  {"in0",c->Array(n,c->BitIn())},
	    {"in1",c->Array(n,c->BitIn())},
	      {"in2",c->Array(n,c->BitIn())},
		{"in3",c->Array(n,c->BitIn())},
		  {"out",c->Array(n,c->Bit())}
	});

      Module* and4_n = g->newModuleDecl("And4",and4Type);
      ModuleDef* def = and4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* and_00 = def->addInstance("and00",and2,{{"width", Const(n)}});
      Wireable* and_01 = def->addInstance("and01",and2,{{"width", Const(n)}});
      Wireable* and_1 = def->addInstance("and1",and2,{{"width", Const(n)}});
    
      def->connect(self->sel("in0"), and_00->sel("in0"));
      def->connect(self->sel("in1"), and_00->sel("in1"));
      def->connect(self->sel("in2"), and_01->sel("in0"));
      def->connect(self->sel("in3"), and_01->sel("in1"));

      def->connect(and_00->sel("out"),and_1->sel("in0"));
      def->connect(and_01->sel("out"),and_1->sel("in1"));

      def->connect(and_1->sel("out"),self->sel("out"));
      and4_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      // How to initialize and track values in the interpreter?
      // I think the right way would be to set select values, but
      // that does not deal with registers and memory that need
      // intermediate values
      SimulatorState state(and4_n);
      state.setValue(self->sel("in0"), BitVec(n, 20));
      state.setValue(self->sel("in1"), BitVec(n, 0));
      state.setValue(self->sel("in2"), BitVec(n, 9));
      state.setValue(self->sel("in3"), BitVec(n, 31));

      state.execute();

      BitVec bv(n, 20 & 0 & 9 & 31);
      REQUIRE(state.getValue(self->sel("out")) == bv);
    }
  }

}
