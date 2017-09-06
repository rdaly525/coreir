#include "catch.hpp"

#include "coreir.h"
#include "coreir-passes/analysis/pass_sim.h"
#include "coreir-passes/transform/rungenerators.h"

#include "../src/passes/analysis/output.hpp"
#include "../src/passes/analysis/sim.hpp"
#include "../src/passes/analysis/utils.hpp"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;

namespace CoreIR {

  TEST_CASE("Large circuits for testing") {
    Context* c = newContext();
    Namespace* g = c->getGlobal();

    SECTION("Many logical operations in parallel") {
      uint n = 32;
      uint numInputs = 100;
  
      Generator* and2 = c->getGenerator("coreir.and");
      Generator* or2 = c->getGenerator("coreir.or");

      // Define Add4 Module
      Type* manyOpsType = c->Record({
	  {"in", c->Array(numInputs, c->Array(n,c->BitIn()))},
	    {"out", c->Array(numInputs - 1, c->Array(n, c->Bit()))}
	});

      Module* manyOps = g->newModuleDecl("manyOps", manyOpsType);

      ModuleDef* def = manyOps->newModuleDef();

      Wireable* self = def->sel("self");

      for (uint i = 0; i < numInputs - 1; i++) {
	Wireable* op;
	if ((i % 2) == 0) {
	  op =
	    def->addInstance("and_" + to_string(i), and2, {{"width", c->argInt(n)}});
	} else {
	  op =
	    def->addInstance("or_" + to_string(i), or2, {{"width", c->argInt(n)}});
	}

	def->connect(self->sel("in")->sel(i), op->sel("in0"));
	def->connect(self->sel("in")->sel(i + 1), op->sel("in1"));

	def->connect(op->sel("out"), self->sel("out")->sel(i));
      }

      manyOps->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(manyOps, g);
      
      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, manyOps);
      int s = compileCode(str, "./gencode/manyops.cpp");

      cout << "Command result = " << s << endl;

      REQUIRE(s == 0);
      
    }

    deleteContext(c);
  }

}
