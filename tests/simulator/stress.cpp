#include "catch.hpp"

#include <fstream>
#include <string>
#include <iostream>

#include "fuzzing.hpp"

#include "coreir.h"
#include "coreir-passes/analysis/pass_sim.h"
#include "coreir/passes/transform/rungenerators.h"

#include "../src/simulator/output.hpp"
#include "../src/simulator/sim.hpp"
#include "../src/simulator/utils.hpp"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  void setThreadNumbers(NGraph& gr) {
    for (auto& v : gr.getVerts()) {
      WireNode w = gr.getNode(v);

      if (isGraphInput(w)) {
	cout << "Input = " << w.getWire()->toString() << endl;
      	w.setThreadNo(0);
      } else {
      	w.setThreadNo(13);
      }

      //w.setThreadNo(13);

      //cout << "Thread number before setting = " << gr.getNode(v).getThreadNo() << endl;
      gr.addVertLabel(v, w);

      //cout << "Thread number after setting  = " << gr.getNode(v).getThreadNo() << endl;
    }
  }

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
	    def->addInstance("and_" + to_string(i), and2, {{"width", Const::make(c,n)}});
	} else {
	  op =
	    def->addInstance("or_" + to_string(i), or2, {{"width", Const::make(c,n)}});
	}

	def->connect(self->sel("in")->sel(i), op->sel("in0"));
	def->connect(self->sel("in")->sel(i + 1), op->sel("in1"));

	def->connect(op->sel("out"), self->sel("out")->sel(i));
      }

      manyOps->setDef(def);

      SECTION("Compiling code") {
	RunGenerators rg;
	rg.runOnNamespace(g);

	cout << "About to build graph" << endl;

	NGraph gr;
	buildOrderedGraph(manyOps, gr);

	setThreadNumbers(gr);

	cout << "VERT thread nos" << endl;
	for (auto& v : gr.getVerts()) {
	  int tNo = gr.getNode(v).getThreadNo();
	  cout << "Thread number = " << tNo << endl;
	  //assert(tNo == 13);
	}

	cout << "Built ordered graph" << endl;
	deque<vdisc> topoOrder = topologicalSort(gr);

	cout << "Topologically sorted" << endl;

	string randIns =
	  randomSimInputHarness(manyOps);

	cout << "Generating harness" << endl;

	int s =
	  generateHarnessAndRun(topoOrder, gr, manyOps,
				"./gencode/",
				"many_ops",
				"./gencode/auto_harness_many_ops.cpp");

	REQUIRE(s == 0);
      }

    }

    deleteContext(c);
  }

}
