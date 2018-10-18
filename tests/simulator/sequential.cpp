//#define CATCH_CONFIG_MAIN

#include "catch.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/libs/commonlib.h"

#include "coreir/simulator/output.h"
#include "coreir/simulator/simulator.h"
#include "coreir/simulator/utils.h"

#include "fuzzing.hpp"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  vector<vector<vdisc> >
  groupByImplName(const vector<vector<vdisc> >& identicalComps,
                  // May not need this parameter
                  const int width) {
    assert((identicalComps.size() % width) == 0);
    assert(identicalComps.size() > 0);

    vector<vector<vdisc> > groups;
    for (uint i = 0; i < identicalComps[0].size(); i++) {
      vector<vdisc> gp;
      for (int j = 0; j < width; j++) {
        gp.push_back(identicalComps[j][i]);
      }
      groups.push_back(gp);
    }

    cout << "Id comps size = " << concat_all(identicalComps).size() << endl;
    cout << "Grouped size  = " << concat_all(groups).size() << endl;
    assert(concat_all(groups).size() == concat_all(identicalComps).size());

    return groups;
  }

  bool splitNodeEdgesCorrect(const NGraph& g) {

    //assert(false);

    //cout << "Edges" << endl;

    for (auto& ed : g.getEdges()) {
      vdisc source = g.source(ed);
      vdisc target = g.target(ed);

      WireNode sourceNode = g.getNode(source);
      WireNode targetNode = g.getNode(target);

      //cout << (c.first).toString() << " ---> " << (c.second).toString() << endl;

      // Either the first edge is not a register or it is not a receiver
      Wireable* fstParent = g.getNode(source).getWire(); //toSelect(*(c.first.getWire())).getParent();

      bool notRec = !isRegisterInstance(fstParent) ||
      	(sourceNode.isSequential && !(sourceNode.isReceiver));

      if (!notRec) { return false; }

      // Either the second edge is not a register or it is a reciver
      Wireable* sndParent = g.getNode(target).getWire(); //toSelect(*(c.second.getWire())).getParent();
      bool isRec = !isRegisterInstance(sndParent) ||
      	(targetNode.isSequential && targetNode.isReceiver);

      if (!isRec) { return false; }
    }

    return true;

  }

  TEST_CASE("Sequential logic") {

    Context* c = newContext();

    SECTION("Register with fanout 2") {

      uint width = 32;

      Type* regType = c->Record({
          {"clk", c->Named("coreir.clkIn")},
            {"in", c->BitIn()->Arr(width)},
              {"out_0", c->Bit()->Arr(width)},
                {"out_1", c->Bit()->Arr(width)}
        });

      Module* regComb =
        c->getGlobal()->newModuleDecl("regComb", regType);

      ModuleDef* def = regComb->newModuleDef();

      def->addInstance("reg0", "coreir.reg", {{"width", Const::make(c, width)}}, {{"init", Const::make(c, BitVec(width, 24))}});

      def->connect("self.in", "reg0.in");

      def->connect("reg0.out", "self.out_0");
      def->connect("reg0.out", "self.out_1");

      def->connect("self.clk", "reg0.clk");

      regComb->setDef(def);

      if (!saveToFile(c->getGlobal(), "register_fan_out_2_pre_gen.json", regComb)) {
        cout << "Could not save to json!!" << endl;
        c->die();
      }
      
      c->runPasses({"rungenerators", "flatten"});

      if (!saveToFile(c->getGlobal(), "register_fan_out_2.json", regComb)) {
        cout << "Could not save to json!!" << endl;
        c->die();
      }
      
      NGraph g;
      buildOrderedGraph(regComb, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {      
	string outFile = "fanout_2_reg";
        string testFile = "test_" + outFile + ".cpp";
	int s = compileCodeAndRun(topoOrder,
				  g,
				  regComb,
				  "./gencode/",
				  outFile,
                                  testFile);

	REQUIRE(s == 0);
      }
      
    }

    SECTION("Combinational logic before register update, sequential path") {
      uint width = 32;

      Type* regType = c->Record({
          {"clk", c->Named("coreir.clkIn")},
            {"in_0", c->BitIn()->Arr(width)},
              {"in_1", c->BitIn()->Arr(width)},
                {"out_0", c->Bit()->Arr(width)},
        });

      Module* regComb =
        c->getGlobal()->newModuleDecl("regComb", regType);

      ModuleDef* def = regComb->newModuleDef();

      def->addInstance("add0", "coreir.add", {{"width", Const::make(c, width)}});
      def->addInstance("reg0", "coreir.reg", {{"width", Const::make(c, width)}});

      def->connect("self.in_0", "add0.in0");
      def->connect("self.in_1", "add0.in1");

      def->connect("add0.out", "reg0.in");

      def->connect("reg0.out", "self.out_0");

      def->connect("self.clk", "reg0.clk");

      regComb->setDef(def);

      if (!saveToFile(c->getGlobal(), "comb_then_register_seq_only.json", regComb)) {
        cout << "Could not save to json!!" << endl;
        c->die();
      }
      
      // c->runPasses({"rungenerators", "flatten"});
      
      // NGraph g;
      // buildOrderedGraph(regComb, g);

      // deque<vdisc> topoOrder = topologicalSort(g);

      // SECTION("Compile and run") {      
      //   string outFile = "comb_then_reg";
      //   string testFile = "test_" + outFile + ".cpp";
      //   int s = compileCodeAndRun(topoOrder,
      //   			  g,
      //   			  regComb,
      //   			  "./gencode/",
      //   			  outFile,
      //                             testFile);

      //   REQUIRE(s == 0);
      // }
      
    }
    
    SECTION("Combinational logic before register update, combinational and sequential path") {
      uint width = 32;

      Type* regType = c->Record({
          {"clk", c->Named("coreir.clkIn")},
            {"in_0", c->BitIn()->Arr(width)},
              {"in_1", c->BitIn()->Arr(width)},
                {"out_0", c->Bit()->Arr(width)},
                  {"out_1", c->Bit()->Arr(width)}
        });

      Module* regComb =
        c->getGlobal()->newModuleDecl("regComb", regType);

      ModuleDef* def = regComb->newModuleDef();

      def->addInstance("add0", "coreir.add", {{"width", Const::make(c, width)}});
      def->addInstance("reg0", "coreir.reg", {{"width", Const::make(c, width)}});

      def->connect("self.in_0", "add0.in0");
      def->connect("self.in_1", "add0.in1");

      def->connect("add0.out", "self.out_0");
      def->connect("add0.out", "reg0.in");

      def->connect("reg0.out", "self.out_1");

      def->connect("self.clk", "reg0.clk");

      regComb->setDef(def);

      if (!saveToFile(c->getGlobal(), "comb_then_register.json", regComb)) {
        cout << "Could not save to json!!" << endl;
        c->die();
      }
      
      c->runPasses({"rungenerators", "flatten"});
      
      NGraph g;
      buildOrderedGraph(regComb, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {      
	string outFile = "comb_then_reg";
        string testFile = "test_" + outFile + ".cpp";
	int s = compileCodeAndRun(topoOrder,
				  g,
				  regComb,
				  "./gencode/",
				  outFile,
                                  testFile);

	REQUIRE(s == 0);
      }
      
    }

    SECTION("Memory primitive") {
      uint width = 16;
      uint depth = 2;
      uint index = 1;

      Type* memoryType = c->Record({
      	  {"clk", c->Named("coreir.clkIn")},
      	    {"write_data", c->BitIn()->Arr(width)},
      	      {"write_addr", c->BitIn()->Arr(index)},
      		{"write_en", c->BitIn()},
      		  {"read_data", c->Bit()->Arr(width)},
      		    {"read_addr", c->BitIn()->Arr(index)}
      	});

      
      Module* memory = c->getGlobal()->newModuleDecl("memory0", memoryType);
      ModuleDef* def = memory->newModuleDef();

      def->addInstance("m0",
      		       "coreir.mem",
      		       {{"width", Const::make(c, width)},{"depth", Const::make(c, depth)}});
		       //      		       {{"init", Const::make(c, BitVector(width*depth,0))}});

      def->connect("self.clk", "m0.clk");
      def->connect("self.write_en", "m0.wen");
      def->connect("self.write_data", "m0.wdata");
      def->connect("self.write_addr", "m0.waddr");
      def->connect("self.read_data", "m0.rdata");
      def->connect("self.read_addr", "m0.raddr");

      memory->setDef(def);

      c->runPasses({"rungenerators", "flatten"});

      cout << "Building graph" << endl;

      NGraph g;
      buildOrderedGraph(memory, g);

      SECTION("Source mem node in operation graph gets raddr as an input") {
	for (auto& vd : g.getVerts()) {
	  WireNode w = g.getNode(vd);

	  if (w.isSequential && !w.isReceiver) {
	    auto ins = getInputConnections(vd, g);

	    REQUIRE(ins.size() == 1);
	  }
	}
      }
      
      cout << "Done building graph" << endl;

      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {
	int s = compileCodeAndRun(topoOrder,
				  g,
				  memory,
				  "./gencode/",
				  "memory",
				  "test_memory.cpp");

      	REQUIRE(s == 0);
      }
      
    }

    SECTION("Registers with enable, but the enable is connected to a constant") {
      uint n = 5;

      Type* RegType = c->Record({
	  {"en", c->BitIn()},
	    {"out_0", c->Array(n, c->Bit())},
              {"out_1", c->Array(n, c->Bit())},
                {"a", c->Array(n, c->BitIn())},
                  {"clk", c->Named("coreir.clkIn")}
	});

      Module* rg = c->getGlobal()->newModuleDecl("offReg", RegType);

      ModuleDef* def = rg->newModuleDef();

      def->addInstance("r0", "mantle.reg", {{"width", Const::make(c,n)},
            {"has_en", Const::make(c,true)}});
      def->addInstance("r1", "mantle.reg", {{"width", Const::make(c,n)},
            {"has_en", Const::make(c,true)}});

      def->addInstance("en_const",
                       "corebit.const",
                       {{"value", Const::make(c, true)}});

      def->connect("en_const.out", "r0.en");
      def->connect("en_const.out", "r1.en");

      def->connect("self.clk", "r0.clk");
      def->connect("self.clk", "r1.clk");

      def->connect("self.a", "r0.in");
      def->connect("self.a", "r1.in");

      def->connect("r0.out", "self.out_0");
      def->connect("r1.out", "self.out_1");

      rg->setDef(def);

      c->runPasses({"rungenerators", "flatten"});
      
      NGraph g;
      buildOrderedGraph(rg, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {      
	string outFile = "reg_const_enable";

	int s = compileCodeAndRun(topoOrder,
				  g,
				  rg,
				  "./gencode/",
				  outFile,
				  "test_reg_const_enable.cpp");

	REQUIRE(s == 0);

      }
      
    }
    
    SECTION("Non standard width register") {
      uint n = 5;

      Type* RegType = c->Record({
	  {"en", c->BitIn()},
	    {"out", c->Array(n, c->Bit())},
	      {"a", c->Array(n, c->BitIn())},
	      {"clk", c->Named("coreir.clkIn")}
	});

      Module* rg = c->getGlobal()->newModuleDecl("offReg", RegType);

      ModuleDef* def = rg->newModuleDef();

      def->addInstance("r", "mantle.reg", {{"width", Const::make(c,n)}, {"has_en", Const::make(c,true)}});

      def->connect("self.en", "r.en");
      def->connect("self.clk", "r.clk");
      def->connect("self.a", "r.in");
      def->connect("r.out", "self.out");

      rg->setDef(def);

      c->runPasses({"rungenerators", "flatten"});
      
      NGraph g;
      buildOrderedGraph(rg, g);

      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      REQUIRE(splitNodeEdgesCorrect(g));

      SECTION("Compile and run") {      
	string outFile = "reg5";

	int s = compileCodeAndRun(topoOrder,
				  g,
				  rg,
				  "./gencode/",
				  outFile,
				  "test_reg5.cpp");

	REQUIRE(s == 0);

      }

    }

    SECTION("Counter") {

      Type* CounterType = c->Record({
	  {"en",c->BitIn()}, 
	    {"out",c->Bit()->Arr(16)}, //Convenient Arr Type Constructor
	      {"clk",c->Named("coreir.clkIn")}, //Named Ref constructor 
		});

      //Now lets create a module declaration. Declarations are specified separately from the definition
      Module* counter = c->getGlobal()->newModuleDecl("counter",CounterType); //use getGlobalFunction
      ModuleDef* def = counter->newModuleDef();

      Values wArg({{"width", Const::make(c,16)}});
      def->addInstance("ai","coreir.add",wArg); // using <namespace>.<module> notation
      def->addInstance("ci","coreir.const",wArg,{{"value", Const::make(c,BitVector(16, 1))}});

      //Reg has default arguments. en/clr/rst are False by default. Init is also 0 by default
      def->addInstance("ri","mantle.reg",{{"width", Const::make(c,16)},{"has_en", Const::make(c,true)}});
    
      //Connections
      def->connect("self.clk","ri.clk");
      def->connect("self.en","ri.en");
      def->connect("ci.out","ai.in0");
      def->connect("ai.out","ri.in");
      def->connect("ri.out","ai.in1");
      def->connect("ri.out","self.out");

      counter->setDef(def);
      counter->print();
      
      c->runPasses({"rungenerators", "flatten"});

      NGraph g;
      buildOrderedGraph(counter, g);

      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      REQUIRE(splitNodeEdgesCorrect(g));

      SECTION("Compile and run") {      
	string outFile = "counter";

	int s = compileCodeAndRun(topoOrder,
				  g,
				  counter,
				  "./gencode/",
				  outFile,
				  "test_counter.cpp");

	REQUIRE(s == 0);

      }

      SECTION("Compile and run single cycle test") {      
	string outFile = "counter";

	int s = compileCodeAndRun(topoOrder,
				  g,
				  counter,
				  "./gencode/",
				  outFile,
				  "test_counter_one_cycle.cpp");

	REQUIRE(s == 0);

      }
      
    }

    SECTION("Register chain") {

      Type* regChainType = c->Record({
	  {"en",c->BitIn()},
	    {"ap", c->BitIn()->Arr(16)},
	    {"bp", c->BitIn()->Arr(16)},
	    {"out",c->Bit()->Arr(16)}, //Convenient Arr Type Constructor
	      {"clk",c->Named("coreir.clkIn")}, //Named Ref constructor 
		});

      Module* regChain = c->getGlobal()->newModuleDecl("regChain", regChainType);
      ModuleDef* def = regChain->newModuleDef();
      Values wArg({{"width", Const::make(c,16)}});

      def->addInstance("ai", "coreir.add", wArg);
      def->addInstance("r0","mantle.reg",{{"width", Const::make(c,16)},{"has_en", Const::make(c,true)}});
      def->addInstance("r1","mantle.reg",{{"width", Const::make(c,16)},{"has_en", Const::make(c,true)}});
      def->addInstance("r2","mantle.reg",{{"width", Const::make(c,16)},{"has_en", Const::make(c,true)}});
    
      //Connections
      def->connect("self.clk", "r0.clk");
      def->connect("self.clk", "r1.clk");
      def->connect("self.clk", "r2.clk");
      
      def->connect("self.en", "r0.en");
      def->connect("self.en", "r1.en");
      def->connect("self.en", "r2.en");

      def->connect("self.ap", "r0.in");
      def->connect("r0.out","r1.in");
      def->connect("r1.out","r2.in");
      def->connect("r2.out","ai.in0");

      def->connect("self.bp", "ai.in1");

      def->connect("ai.out","self.out");

      regChain->setDef(def);
      regChain->print();
      
      c->runPasses({"rungenerators", "flatten"});

      NGraph g;
      buildOrderedGraph(regChain, g);

      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      SECTION("Compile and run") {
	int s = compileCode(topoOrder, g, regChain, "./gencode/", "register_chain");
	REQUIRE(s == 0);
      }
      
    }

    SECTION("Register without enable") {

      int n = 8;

      Type* regChainType = c->Record({
	  {"a", c->BitIn()->Arr(n)},
	    {"cout",c->Bit()->Arr(n)},
	      {"clk",c->Named("coreir.clkIn")},
		});

      Module* regChain = c->getGlobal()->newModuleDecl("regChain", regChainType);
      ModuleDef* def = regChain->newModuleDef();

      def->addInstance("r0","mantle.reg",{{"width", Const::make(c,n)},{"has_en", Const::make(c,false)}});
    
      //Connections
      def->connect("self.clk", "r0.clk");
      def->connect("self.a", "r0.in");
      def->connect("r0.out","self.cout");

      regChain->setDef(def);

      c->runPasses({"rungenerators", "flatten"});

      NGraph g;
      buildOrderedGraph(regChain, g);

      SECTION("Checking number of vertices") {
	REQUIRE(splitNodeEdgesCorrect(g));	
      }

      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      SECTION("Compile and run") {
	int s = compileCode(topoOrder, g, regChain, "./gencode/", "register_no_enable");
	REQUIRE(s == 0);
      }
    }

    SECTION("Long (103 bit) Register without enable") {

      int n = 103;

      Type* regChainType = c->Record({
	  {"a", c->BitIn()->Arr(n)},
	    {"cout",c->Bit()->Arr(n)},
	      {"clk",c->Named("coreir.clkIn")},
		});

      Module* regChain = c->getGlobal()->newModuleDecl("regChain", regChainType);
      ModuleDef* def = regChain->newModuleDef();

      def->addInstance("r0","mantle.reg",{{"width", Const::make(c,n)},{"has_en", Const::make(c,false)}});
    
      //Connections
      def->connect("self.clk", "r0.clk");
      def->connect("self.a", "r0.in");
      def->connect("r0.out","self.cout");

      regChain->setDef(def);
      
      c->runPasses({"rungenerators", "flatten"});

      NGraph g;
      buildOrderedGraph(regChain, g);

      SECTION("Checking number of vertices") {
	REQUIRE(splitNodeEdgesCorrect(g));	
      }

      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      SECTION("Compile code") {

	int s =
	  compileCode(topoOrder,
		      g,
		      regChain,
		      "./gencode/",
		      "long_register_no_enable"); //compileCode(str, outFile);

	REQUIRE(s == 0);
      }
    }

    SECTION("Clock array") {
      uint n = 16;
      uint nRegs = 3;

      Type* clkArrayType = c->Record({
	  {"clkArr", c->Array(nRegs, c->Named("coreir.clkIn"))},
	    {"a", c->Array(nRegs, c->Array(n, c->BitIn()))},
	      {"b", c->Array(nRegs, c->Array(n, c->Bit()))}
	});

      Module* clkArr = c->getGlobal()->newModuleDecl("clkArr", clkArrayType);

      ModuleDef* def = clkArr->newModuleDef();
      Wireable* self = def->sel("self");

      for (uint i = 0; i < nRegs; i++) {
	string rName = "r" + to_string(i);
	Wireable* r = def->addInstance(rName,
				       "mantle.reg",
				       {{"width", Const::make(c,n)},
					   {"has_en", Const::make(c,false)}});

	def->connect(self->sel("clkArr")->sel(i), r->sel("clk"));
	def->connect(self->sel("a")->sel(i), r->sel("in"));

	def->connect(r->sel("out"), self->sel("b")->sel(i));
      }

      clkArr->setDef(def);

      c->runPasses({"rungenerators", "flatten"});

      cout << "Building graph" << endl;

      NGraph g;
      buildOrderedGraph(clkArr, g);

      cout << "Done building graph" << endl;

      SECTION("Checking number of vertices") {
	REQUIRE(splitNodeEdgesCorrect(g));	
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {
	int s = compileCode(topoOrder, g, clkArr, "./gencode/", "clock_array");
	REQUIRE(s == 0);
      }
      
    }

    /*
    SECTION("LineBufferMem") {

      uint index = 4;
      uint width = index;
      uint depth = pow(2, index) - 6;

      CoreIRLoadLibrary_commonlib(c);

      Type* lineBufferMemType = c->Record({
          {"clk", c->Named("coreir.clkIn")},
            {"wdata", c->BitIn()->Arr(width)},
              {"rdata", c->Bit()->Arr(width)},
                {"wen", c->BitIn()},
        	  {"valid", c->Bit()}
        });

      Module* lbMem = c->getGlobal()->newModuleDecl("lbMem", lineBufferMemType);
      ModuleDef* def = lbMem->newModuleDef();

      def->addInstance("lb_wen", "corebit.const", {{"value", Const::make(c, true)}});
      def->addInstance("m0",
        	       "memory.rowbuffer",
        	       {{"width", Const::make(c, width)},
        		   {"depth", Const::make(c, depth)}});

      def->connect("self.clk", "m0.clk");
      //def->connect("lb_wen.out", "m0.wen");
      def->connect("self.wen", "m0.wen");
      
      def->connect("self.wdata", "m0.wdata");
      def->connect("m0.rdata", "self.rdata");
      def->connect("m0.valid", "self.valid");

      lbMem->setDef(def);
      
      c->runPasses({"rungenerators","flattentypes","flatten"});

      Module* m = lbMem;

      NGraph g;
      buildOrderedGraph(m, g);
      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {
	int s = compileCodeAndRun(topoOrder,
                                  g,
                                  m,
                                  "./gencode/",
                                  "lbMem",
                                  "test_lbMem.cpp");
	REQUIRE(s == 0);
      }
    }
    */

    // SECTION("Harris") {
    //   CoreIRLoadLibrary_commonlib(c);

    //   if (!loadFromFile(c,"./harris.json")) {
    // 	cout << "Could not Load from json!!" << endl;
    // 	c->die();
    //   }


    //   cout << "==== HARRIS Graph" << endl;
    //   Module* mPre = c->getGlobal()->getModule("DesignTop");
    //   NGraph preG;
    //   buildOrderedGraph(mPre, preG);

    //   auto preOrder = topologicalSort(preG);

    //   cout << "Pre topological order = " << endl;
    //   for (auto& vd : preOrder) {
    //     cout << preG.getNode(vd).getWire()->toString() << " has " << preG.outEdges(vd).size() << " outputs " << endl;
    //   }

    //   auto preLevels = topologicalLevels(preG);

    //   cout << "Pre topological order = " << endl;
    //   for (auto& level : preLevels) {
    //     cout << "------- Level" << endl;
    //     for (auto& vd : level) {
    //       WireNode wd = preG.getNode(vd);
    //       cout << wd.getWire()->toString() << " : " << wd.getWire()->getType()->toString() << endl;
          
    //     }
    //   }

    //   c->runPasses({"rungenerators","flattentypes", "flatten", "wireclocks-coreir"});
    //   Module* m = c->getGlobal()->getModule("DesignTop");

    //   map<int, vector<vdisc>> numOutputsHisto;
    //   NGraph g;
    //   buildOrderedGraph(m, g);
    //   auto postLevels = topologicalLevels(g);
    //   cout << "Pre topological order = " << endl;
    //   for (auto& level : postLevels) {
    //     cout << "------- Level" << endl;
    //     for (auto& vd : level) {
    //       WireNode wd = g.getNode(vd);
    //       cout << wd.getWire()->toString() << " : " << wd.getWire()->getType()->toString() << " has " << g.outEdges(vd).size() << " outputs" << endl;
          

    //       map_insert(numOutputsHisto, (int) g.outEdges(vd).size(), vd);
    //     }
    //   }

    //   cout << "Fan out distribution" << endl;
    //   for (auto& ent : numOutputsHisto) {
    //     cout << ent.first << " --> " << ent.second.size() << endl;
    //   }

    //   // Finding all nodes from each of the lb grads
    //   vector<vdisc> grad_xx_nodes;
    //   vector<vdisc> grad_xy_nodes;
    //   vector<vdisc> grad_yy_nodes;

    //   for (auto& vd : concat_all(postLevels)) {
    //     Wireable* w = g.getNode(vd).getWire();
    //     if (isInstance(w)) {
    //       Instance* inst = toInstance(w);

    //       string instName = inst->toString();
    //       string origin = instName.substr(0, instName.find("$"));

    //       if (origin == "lb_grad_yy_2_stencil_update_stream") {
    //         grad_yy_nodes.push_back(vd);
    //       }

    //       if (origin == "lb_grad_xx_2_stencil_update_stream") {
    //         grad_xx_nodes.push_back(vd);
    //       }

    //       if (origin == "lb_grad_xy_2_stencil_update_stream") {
    //         grad_xy_nodes.push_back(vd);
    //       }
          
    //     }
    //   }

    //   cout << "---- gradient linebuffers" << endl;
    //   cout << "---- yy elems = " << grad_yy_nodes.size() << endl;
    //   for (auto& vd : grad_yy_nodes) {
    //     cout << nodeString(g.getNode(vd)) << endl;
    //   }
    //   cout << "---- xx elems = " << grad_xx_nodes.size() << endl;
    //   for (auto& vd : grad_xx_nodes) {
    //     cout << nodeString(g.getNode(vd)) << endl;
    //   }
    //   cout << "---- xy elems size = " << grad_xy_nodes.size() << endl;
    //   for (auto& vd : grad_xy_nodes) {
    //     cout << nodeString(g.getNode(vd)) << endl;
    //   }

    //   vector<vector<vdisc> > identicalComps;
    //   identicalComps.push_back(grad_xx_nodes);
    //   identicalComps.push_back(grad_yy_nodes);
    //   identicalComps.push_back(grad_xy_nodes);

    //   vector<vector<vdisc> > simdGroups =
    //     groupByImplName(identicalComps, 3);

    //   vector<vdisc> internalNodes = concat_all(simdGroups);
    //   vector<vdisc> stagedInputs;
    //   vector<vdisc> stagedOutputs;

    //   for (auto& comp : simdGroups) {
    //     cout << "--- Group" << endl;
    //     for (auto& vd : comp) {
    //       cout << "\t" << nodeString(g.getNode(vd)) << endl;
    //     }

    //     cout << "--- Group inputs" << endl;
    //     for (auto& vd : comp) {
    //       for (auto& inConn : g.inEdges(vd)) {
    //         auto inVD = g.source(inConn);
    //         cout << "\t\t" << nodeString(g.getNode(inVD)) << endl;

    //         if (!elem(inVD, internalNodes) && !elem(inVD, stagedInputs)) {
    //           stagedInputs.push_back(inVD);
    //         }
    //       }
    //     }

    //     cout << "--- Group outputs" << endl;
    //     for (auto& vd : comp) {
    //       for (auto& inConn : g.outEdges(vd)) {
    //         auto inVD = g.target(inConn);
    //         cout << "\t\t" << nodeString(g.getNode(inVD)) << endl;

    //         if (!elem(inVD, internalNodes) && !elem(inVD, stagedOutputs)) {
    //           stagedOutputs.push_back(inVD);
    //         }
    //       }
    //     }

    //   }

    //   cout << "# of inputs to stage = " << stagedInputs.size() << endl;
    //   for (auto& vd : stagedInputs) {
    //     cout << "\t" << nodeString(g.getNode(vd)) << endl;
    //   }

    //   cout << "# of outputs to stage = " << stagedOutputs.size() << endl;
    //   for (auto& vd : stagedOutputs) {
    //     cout << "\t" << nodeString(g.getNode(vd)) << endl;
    //   }
      
      
    // }
    /*
    SECTION("conv_3_1") {
      CoreIRLoadLibrary_commonlib(c);

      if (!loadFromFile(c,"./conv_3_1.json")) {
    	cout << "Could not Load from json!!" << endl;
    	c->die();
      }


      Module* mPre = c->getGlobal()->getModule("DesignTop");
      NGraph preG;
      buildOrderedGraph(mPre, preG);

      auto preOrder = topologicalSort(preG);

      cout << "Pre topological order = " << endl;
      for (auto& vd : preOrder) {
        cout << preG.getNode(vd).getWire()->toString() << endl;
      }

      auto preLevels = topologicalLevels(preG);

      cout << "Pre topological order = " << endl;
      for (auto& level : preLevels) {
        cout << "------- Level" << endl;
        for (auto& vd : level) {
          cout << preG.getNode(vd).getWire()->toString() << endl;
        }
      }
      
      c->runPasses({"rungenerators","flattentypes","flatten", "wireclocks-coreir"});

      Module* m = c->getGlobal()->getModule("DesignTop");

      NGraph g;
      buildOrderedGraph(m, g);
      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {
	int s = compileCodeAndRun(topoOrder,
                                  g,
                                  m,
                                  "./gencode/",
                                  "conv_3_1",
                                  "test_conv_3_1.cpp");
	REQUIRE(s == 0);
      }
        
    }
    */
    deleteContext(c);

  }
  
}
