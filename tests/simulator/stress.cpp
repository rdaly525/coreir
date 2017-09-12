#include "catch.hpp"

#include <fstream>
#include <string>
#include <iostream>

#include "fuzzing.hpp"

#include "coreir.h"
#include "coreir-passes/analysis/pass_sim.h"
#include "coreir-passes/transform/rungenerators.h"

#include "../src/simulator/output.hpp"
#include "../src/simulator/sim.hpp"
#include "../src/simulator/utils.hpp"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;

namespace CoreIR {

  TEST_CASE("Large circuits for testing") {
    Context* c = newContext();
    Namespace* g = c->getGlobal();

    SECTION("Many logical operations in parallel") {
      uint n = 31;
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

      SECTION("Compiling code") {
	RunGenerators rg;
	rg.runOnNamespace(g);

	cout << "About to build graph" << endl;

	NGraph gr;
	buildOrderedGraph(manyOps, gr);

	cout << "Built ordered graph" << endl;
      
	deque<vdisc> topoOrder = topologicalSort(gr);

	cout << "Topologically sorted" << endl;

	string randIns =
	  randomSimInputHarness(manyOps);

	cout << "Generating harness" << endl;

	int s =
	  generateHarnessAndRun(topoOrder, gr, manyOps,
				"./gencode/many_ops",
				"./gencode/auto_harness_many_ops.cpp");

	REQUIRE(s == 0);
      }

      // Building verilog example

      string jsonFile = "manyOps.json";
      // Save to json
      saveToFile(g, jsonFile);

      // Use coreir to build json into
      string runCmd = "../../bin/coreir -i manyOps.json -o manyOps.v";
      int s = system(runCmd.c_str());

      REQUIRE(s == 0);

      std::ifstream t("manyOps.v");
      std::string str((std::istreambuf_iterator<char>(t)),
		      std::istreambuf_iterator<char>());

      str = "`include \"stdlib.v\"\n" + str;

      std::ofstream out("manyOps.v");
      out << str;
      out.close();      
      
      // Run verilator on the resulting file
      string compileVerilator = "verilator -O3 -Wall -Wno-DECLFILENAME --cc manyOps.v --exe ./gencode/manyOpMain.cpp --top-module manyOps";


      s = system(compileVerilator.c_str());


      REQUIRE(s == 0);

      string compileCpp = "make -C obj_dir -j -f VmanyOps.mk VmanyOps";
      s = system(compileCpp.c_str());

      REQUIRE(s == 0);

      string runObj = "./obj_dir/VmanyOps";
      s = system(runObj.c_str());

      REQUIRE(s == 0);

    }

    deleteContext(c);
  }

}
