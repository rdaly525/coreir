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

    SECTION("Add 4") {
      cout << "32 bit add 4" << endl;

      uint n = 32;
  
      Generator* add2 = c->getGenerator("coreir.add");

      // Define Add4 Module
      Type* add4Type = c->Record({
	  {"in0",c->Array(n,c->BitIn())},
	    {"in1",c->Array(n,c->BitIn())},
	      {"in2",c->Array(n,c->BitIn())},
		{"in3",c->Array(n,c->BitIn())},
		  {"out",c->Array(n,c->Bit())}
	});

      Module* add4_n = g->newModuleDecl("Add4",add4Type);
      ModuleDef* def = add4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* add_00 = def->addInstance("add00",add2,{{"width", Const(n)}});
      Wireable* add_01 = def->addInstance("add01",add2,{{"width", Const(n)}});
      Wireable* add_1 = def->addInstance("add1",add2,{{"width", Const(n)}});
    
      def->connect(self->sel("in0"), add_00->sel("in0"));
      def->connect(self->sel("in1"), add_00->sel("in1"));
      def->connect(self->sel("in2"), add_01->sel("in0"));
      def->connect(self->sel("in3"), add_01->sel("in1"));

      def->connect(add_00->sel("out"),add_1->sel("in0"));
      def->connect(add_01->sel("out"),add_1->sel("in1"));

      def->connect(add_1->sel("out"),self->sel("out"));
      add4_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph gr;
      buildOrderedGraph(add4_n, gr);
      deque<vdisc> topoOrder = topologicalSort(gr);

      // How to initialize and track values in the interpreter?
      // I think the right way would be to set select values, but
      // that does not deal with registers and memory that need
      // intermediate values
      SimulatorState state;
      state.setValue(self->sel("in0"), BitVec(n, 20));
      state.setValue(self->sel("in1"), BitVec(n, 0));
      state.setValue(self->sel("in2"), BitVec(n, 9));
      state.setValue(self->sel("in3"), BitVec(n, 31));

      state.execute();

      BitVec bv(n, 20 + 0 + 9 + 31);
      REQUIRE(state.getValue(self->sel("out")) == bv);
    }
  }

}
