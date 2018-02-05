#define CATCH_CONFIG_MAIN

#include "catch.hpp"

#include <fstream>
#include <string>
#include <iostream>

#include "fuzzing.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/simulator/interpreter.h"

#include "coreir/simulator/multithreading.h"
#include "coreir/simulator/output.h"
#include "coreir/simulator/simulator.h"
#include "coreir/simulator/utils.h"

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
      uint n = 16;
      //uint numOutputs = 100000;
      //uint numOutputs = 10000;
      uint numOutputs = 32;
      uint numInputs = numOutputs*2;
  
      Generator* and2 = c->getGenerator("coreir.and");
      Generator* or2 = c->getGenerator("coreir.or");

      // Define Add4 Module
      RecordParams opParams = {
        {"clk", c->Named("coreir.clkIn")}};

      cout << "Creating recordparams" << endl;
      for (uint i = 0; i < numInputs; i++) {
        opParams.push_back({"in_" + to_string(i), c->Array(n,c->BitIn())});
      }

      for (uint i = 0; i < numOutputs; i++) {
        opParams.push_back({"out_" + to_string(i), c->Array(n, c->Bit())});
      }

      cout << "Creating module" << endl;

      Type* manyOpsType = c->Record(opParams);
      Module* manyOps = g->newModuleDecl("manyOps", manyOpsType);
      ModuleDef* def = manyOps->newModuleDef();
      Wireable* self = def->sel("self");

      
      cout << "Wiring up inputs" << endl;

      vector<Wireable*> ops;
      vector<Wireable*> regs;
      for (uint i = 0; i < numOutputs; i++) {
	Wireable* op;
	if ((i % 2) == 0) {
	  op =
	    def->addInstance("and_" + to_string(i), and2, {{"width", Const::make(c,n)}});
	} else {
	  op =
	    def->addInstance("or_" + to_string(i), or2, {{"width", Const::make(c,n)}});
	}

        auto reg = def->addInstance("reg_" + to_string(i),
                                    "coreir.reg",
                                    {{"width", Const::make(c, n)}});

        ops.push_back(op);
        regs.push_back(reg);

      }

      cout << "Created ALL instances" << endl;

      cout << "Creating dummy selects" << endl;

      for (uint i = 0; i < numOutputs; i++) {

        auto op = ops[i];
        auto reg = regs[i];

	auto s1 = self->sel("in_" + to_string(2*i));
        auto s2 = op->sel("in0");
	auto s3 = self->sel("in_" + to_string(2*i + 1));
        auto s4 = op->sel("in1");

        auto s5 = op->sel("out");
        auto s6 = reg->sel("in");
        auto s7 = self->sel("clk");
        auto s8 = reg->sel("clk");

	auto s9 = reg->sel("out");
        auto s10 = self->sel("out_" + to_string(i));

        if ((i % 1000) == 0) {
          cout << "Selects " << i << "!!!" << endl;
        }

      }

      cout << "Done with selects" << endl;

      for (uint i = 0; i < numOutputs; i++) {

        auto op = ops[i];
        auto reg = regs[i];

	def->connect(self->sel("in_" + to_string(2*i)), op->sel("in0"));
	def->connect(self->sel("in_" + to_string(2*i + 1)), op->sel("in1"));

        def->connect(op->sel("out"), reg->sel("in"));
        def->connect(self->sel("clk"), reg->sel("clk"));

	def->connect(reg->sel("out"), self->sel("out_" + to_string(i)));

        if ((i % 1000) == 0) {
          cout << "Wired up inputs " << i << endl;
        }
      }
      
      cout << "Setting definition" << endl;

      //assert(false);

      manyOps->setDef(def);

      cout << "Running passes" << endl;

      c->runPasses({"rungenerators"}); //, "flattentypes"})"flatten"});

      cout << "Writing to json" << endl;
      if (!saveToFile(g, "many_ops.json", manyOps)) {
        cout << "Could not save to json!!" << endl;
        c->die();
      }

      // Simulation code

      // SECTION("Interpreting code") {
      //   cout << "Starting passes" << endl;
      //   cout << "Done with passes" << endl;
      //   cout << "Setting up interpreter" << endl;

      //   SimulatorState state(manyOps);

      // }
      
      NGraph gr;
      buildOrderedGraph(manyOps, gr);

      //balancedComponentsParallel(gr);

      cout << "Starting manyOpsological sort" << endl;

      // Delete inputs from the order, since they do not need to
      // be printed out
      deque<vdisc> topoOrder = topologicalSort(gr);

      string codePath = "./gencode/";
      string codeFile = manyOps->getName() + "_sim.cpp";
      string hFile = manyOps->getName() + "_sim.h";

      // writeBitVectorLib(codePath + "bit_vector.h");

      // cout << "Writing out files" << endl;

      //writeFiles(topoOrder, gr, manyOps, codePath, codeFile, hFile);
      

      int s = compileCodeAndRun(topoOrder, gr, manyOps, "./gencode/", "manyOps_sim", "test_manyOps_sim.cpp");

      REQUIRE(s == 0);
      // SECTION("Compiling code") {
      //   c->runPasses({"rungenerators", "flattentypes"});

      // 	cout << "About to build graph" << endl;

      // 	NGraph gr;
      // 	buildOrderedGraph(manyOps, gr);

      //   SECTION("3 topological levels") {
      //     vector<vector<vdisc>> topoLevels =
      //       topologicalLevels(gr);

      //     REQUIRE(topoLevels.size() == 3);
      //   }

      // 	setThreadNumbers(gr);

      // 	cout << "Built ordered graph" << endl;
      // 	deque<vdisc> topoOrder = topologicalSort(gr);

      // 	cout << "Topologically sorted" << endl;

      // 	string randIns =
      // 	  randomSimInputHarness(manyOps);

      // 	cout << "Generating harness" << endl;

      // 	int s =
      // 	  generateHarnessAndRun(topoOrder, gr, manyOps,
      // 				"./gencode/",
      // 				"many_ops",
      // 				"./gencode/auto_harness_many_ops.cpp");

      // 	REQUIRE(s == 0);
      // }

    }

    deleteContext(c);
  }

}
