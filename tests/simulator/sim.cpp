#define CATCH_CONFIG_MAIN

#include "catch.hpp"

#include "coreir.h"
#include "coreir-passes/analysis/pass_sim.h"
#include "coreir-passes/transform/rungenerators.h"

#include "../src/passes/analysis/sim.hpp"
#include "../src/passes/analysis/utils.hpp"

#include <iostream>
#include <fstream>

using namespace CoreIR;
using namespace CoreIR::Passes;

int compileCode(const std::string& code, const std::string& outFile) {
  std::ofstream out(outFile);
  out << code;
  out.close();


  string runCmd = "clang -c " + outFile;
  int s = system(runCmd.c_str());

  cout << "Command result = " << s << endl;

  return s;

}

void writeFiles(const std::deque<vdisc>& topoOrder,
		NGraph& g,
		Module* mod,
		const std::string& codeFile,
		const std::string& hFile) {
  string codeStr = printCode(topoOrder, g, mod);
  string hStr = printDecl(mod);

  std::ofstream out(codeFile);
  out << codeStr;
  out.close();

  std::ofstream outH(hFile);
  outH << hStr;
  outH.close();

}

int compileCodeAndRun(const std::deque<vdisc>& topoOrder,
		      NGraph& g,
		      Module* mod,
		      const std::string& outFile,
		      const std::string& harnessFile) {

  string hFile = outFile + ".h";
  string codeFile = outFile + ".c";

  writeFiles(topoOrder, g, mod, codeFile, hFile);
  
  string runCmd = "clang " + codeFile + " " + harnessFile;
  int s = system(runCmd.c_str());

  cout << "Command result = " << s << endl;

  string runTest = "./a.out";
  int r = system(runTest.c_str());

  cout << "Test result = " << r << endl;

  return s || r;
}

int compileCodeAndRun(const std::string& code,
		      const std::string& outFile,
		      const std::string& harnessFile) {
  std::ofstream out(outFile);
  out << code;
  out.close();

  string runCmd = "clang " + outFile + " " + harnessFile;
  int s = system(runCmd.c_str());

  cout << "Command result = " << s << endl;

  //return s;

  string runTest = "./a.out";
  int r = system(runTest.c_str());

  cout << "Test result = " << r << endl;

  return s || r;
}  

namespace CoreIR {

  TEST_CASE("Combinational logic simulation") {

    // New context
    Context* c = newContext();
  
    Namespace* g = c->getGlobal();
    
    SECTION("32 bit add 4") {
      uint n = 32;
  
      Generator* add2 = c->getGenerator("coreir.add");

      // Define Add4 Module
      Type* add4Type = c->Record({
	  {"in",c->Array(4,c->Array(n,c->BitIn()))},
	    {"out",c->Array(n,c->Bit())}
	});

      Module* add4_n = g->newModuleDecl("Add4",add4Type);
      ModuleDef* def = add4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* add_00 = def->addInstance("add00",add2,{{"width",c->argInt(n)}});
      Wireable* add_01 = def->addInstance("add01",add2,{{"width",c->argInt(n)}});
      Wireable* add_1 = def->addInstance("add1",add2,{{"width",c->argInt(n)}});
    
      def->connect(self->sel("in")->sel(0),add_00->sel("in0"));
      def->connect(self->sel("in")->sel(1),add_00->sel("in1"));
      def->connect(self->sel("in")->sel(2),add_01->sel("in0"));
      def->connect(self->sel("in")->sel(3),add_01->sel("in1"));

      def->connect(add_00->sel("out"),add_1->sel("in0"));
      def->connect(add_01->sel("out"),add_1->sel("in1"));

      def->connect(add_1->sel("out"),self->sel("out"));
      add4_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(add4_n, g);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(g) == 5);
      }
      
      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, add4_n);
      int s = compileCode(str, "./gencode/add4.c");

      cout << "Command result = " << s << endl;

      REQUIRE(s == 0);

    }

    SECTION("64 bit subtract") {
      uint n = 64;
  
      Generator* sub2 = c->getGenerator("coreir.sub");

      Type* sub4Type = c->Record({
	  {"in",c->Array(4,c->Array(n,c->BitIn()))},
	    {"out",c->Array(n,c->Bit())}
	});

      Module* sub4_n = g->newModuleDecl("Sub4",sub4Type);
      ModuleDef* def = sub4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* sub_00 = def->addInstance("sub00",sub2,{{"width",c->argInt(n)}});
      Wireable* sub_01 = def->addInstance("sub01",sub2,{{"width",c->argInt(n)}});
      Wireable* sub_1 = def->addInstance("sub1",sub2,{{"width",c->argInt(n)}});
    
      def->connect(self->sel("in")->sel(0),sub_00->sel("in0"));
      def->connect(self->sel("in")->sel(1),sub_00->sel("in1"));
      def->connect(self->sel("in")->sel(2),sub_01->sel("in0"));
      def->connect(self->sel("in")->sel(3),sub_01->sel("in1"));

      def->connect(sub_00->sel("out"),sub_1->sel("in0"));
      def->connect(sub_01->sel("out"),sub_1->sel("in1"));

      def->connect(sub_1->sel("out"),self->sel("out"));
      sub4_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(sub4_n, g);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(g) == 5);
      }
      
      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, sub4_n);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      string outFile = "./gencode/sub4.c";
      std::ofstream out(outFile);
      out << str;
      out.close();

      string runCmd = "clang -c " + outFile;
      int s = system(runCmd.c_str());

      cout << "Command result = " << s << endl;

      REQUIRE(s == 0);
    }

    SECTION("Multiply 8 bits") {

      uint n = 8;
  
      Generator* mul2 = c->getGenerator("coreir.mul");

      Type* mul2Type = c->Record({
	  {"in",c->Array(2,c->Array(n,c->BitIn()))},
	    {"out",c->Array(n,c->Bit())}
	});

      Module* mul_n = g->newModuleDecl("Mul4", mul2Type);
      ModuleDef* def = mul_n->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* mul = def->addInstance("mul1", mul2, {{"width", c->argInt(n)}});
    
      def->connect(self->sel("in")->sel(0), mul->sel("in0"));
      def->connect(self->sel("in")->sel(1), mul->sel("in1"));

      def->connect(mul->sel("out"), self->sel("out"));
      mul_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(mul_n, g);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(g) == 3);
      }
      
      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, mul_n);
      cout << "CODE STRING" << endl;
      cout << str << endl;
      int s = compileCode(str, "./gencode/mul2.c");

      cout << "Command result = " << s << endl;

      REQUIRE(s == 0);

    }

    SECTION("One 37 bit logical and") {
      uint n = 37;

      Generator* andG = c->getGenerator("coreir.and");

      Type* andType = c->Record({
	  {"input", c->Array(2, c->Array(n, c->BitIn()))},
	    {"output", c->Array(n, c->Bit())}
	});

      Module* andM = g->newModuleDecl("and37", andType);

      ModuleDef* def = andM->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* and0 = def->addInstance("and0", andG, {{"width", c->argInt(n)}});

      def->connect("self.input.0", "and0.in0");
      def->connect("self.input.1", "and0.in1");
      def->connect("and0.out", "self.output");

      andM->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(andM, g);

      SECTION("Checking graph size") {
      	REQUIRE(numVertices(g) == 3);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, andM);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      string outFile = "./gencode/and37.c";

      int s = compileCodeAndRun(topoOrder,
				g,
				andM,
				"./gencode/and37",
				"./gencode/test_and37.c");

      cout << "Test result = " << s << endl;

      REQUIRE(s == 0);
      
    }

    SECTION("One 63 bit addition") {
      uint n = 63;

      Generator* addG = c->getGenerator("coreir.add");

      Type* addType = c->Record({
	  {"input", c->Array(2, c->Array(n, c->BitIn()))},
	    {"output", c->Array(n, c->Bit())}
	});

      Module* addM = g->newModuleDecl("add63", addType);

      ModuleDef* def = addM->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* add0 = def->addInstance("add0", addG, {{"width", c->argInt(n)}});

      def->connect("self.input.0", "add0.in0");
      def->connect("self.input.1", "add0.in1");
      def->connect("add0.out", "self.output");

      addM->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(addM, g);

      SECTION("Checking graph size") {
      	REQUIRE(numVertices(g) == 3);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, addM);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      string outFile = "./gencode/add63";
      int s = compileCodeAndRun(topoOrder,
				g,
				addM,
				outFile,
				"./gencode/test_add63.c");

      REQUIRE(s == 0);

    }

    SECTION("One 2 bit not") {
      uint n = 2;
  
      Generator* neg = c->getGenerator("coreir.not");

      Type* neg2Type = c->Record({
	  {"A",    c->Array(n,c->BitIn())},
	    {"res", c->Array(n,c->Bit())}
	});

      Module* neg_n = g->newModuleDecl("neg_16", neg2Type);

      ModuleDef* def = neg_n->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* neg0 = def->addInstance("neg0", neg, {{"width", c->argInt(n)}});

      def->connect(self->sel("A"), neg0->sel("in"));

      def->connect(neg0->sel("out"), self->sel("res"));

      neg_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      Type* t = neg_n->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph g;
      buildOrderedGraph(neg_n, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, neg_n);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      string outFile = "./gencode/neg2";
      int s = compileCodeAndRun(topoOrder,
				g,
				neg_n,
				outFile,
				"./gencode/test_neg2.c");

      REQUIRE(s == 0);

      
    }
    
    SECTION("One 16 bit not") {
      uint n = 16;
  
      Generator* neg = c->getGenerator("coreir.not");

      Type* neg2Type = c->Record({
	  {"A",    c->Array(n,c->BitIn())},
	    {"res", c->Array(n,c->Bit())}
	});

      Module* neg_n = g->newModuleDecl("neg_16", neg2Type);

      ModuleDef* def = neg_n->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* neg0 = def->addInstance("neg0", neg, {{"width", c->argInt(n)}});

      def->connect(self->sel("A"), neg0->sel("in"));

      def->connect(neg0->sel("out"), self->sel("res"));

      neg_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      Type* t = neg_n->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph g;
      buildOrderedGraph(neg_n, g);

      SECTION("Checking graph size") {
      	REQUIRE(numVertices(g) == 3);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, neg_n);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      int s = compileCode(str, "./gencode/neg16.c");

      cout << "Command result = " << s << endl;

      REQUIRE(s == 0);
    }
    
    SECTION("Two 16 bit nots") {
      uint n = 16;
  
      Generator* neg = c->getGenerator("coreir.not");

      Type* neg2Type = c->Record({
	  {"in",    c->Array(2, c->Array(n,c->BitIn()))},
	    {"out", c->Array(2, c->Array(n,c->Bit()))}
	});

      Module* neg_n = g->newModuleDecl("two_negs", neg2Type);

      ModuleDef* def = neg_n->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* neg0 = def->addInstance("neg0", neg, {{"width", c->argInt(n)}});
      Wireable* neg1 = def->addInstance("neg1", neg, {{"width", c->argInt(n)}});

      def->connect(self->sel("in")->sel(0), neg0->sel("in"));
      def->connect(self->sel("in")->sel(1), neg1->sel("in"));

      def->connect(neg0->sel("out"), self->sel("out")->sel(0));
      def->connect(neg1->sel("out"), self->sel("out")->sel(1));

      neg_n->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      Type* t = neg_n->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph g;
      buildOrderedGraph(neg_n, g);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(g) == 4);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, neg_n);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      int s = compileCode(str, "./gencode/two_negs.c");

      cout << "Command result = " << s << endl;

      REQUIRE(s == 0);
      
    }

    SECTION("Add 2 by 3 64 bit matrices") {
      uint n = 64;
  
      Generator* add = c->getGenerator("coreir.add");

      Type* addMatsType = c->Record({
	  {"A",    c->Array(2, c->Array(3, c->Array(n,c->BitIn()))) },
	    {"B",    c->Array(2, c->Array(3, c->Array(n,c->BitIn()))) },
	      {"out", c->Array(2, c->Array(3, c->Array(n,c->Bit()))) }
	});

      Module* addM = g->newModuleDecl("two_negs", addMatsType);

      ModuleDef* def = addM->newModuleDef();

      Wireable* self = def->sel("self");
      for (int i = 0; i < 2; i++) {
	for (int j = 0; j < 3; j++) {
	  string str = "add" + to_string(i) + "_" + to_string(j);
	  Wireable* addInst = def->addInstance(str, add, {{"width", c->argInt(n)}});

	  def->connect(self->sel("A")->sel(i)->sel(j), addInst->sel("in0"));
	  def->connect(self->sel("B")->sel(i)->sel(j), addInst->sel("in1"));

	  def->connect(addInst->sel("out"), self->sel("out")->sel(i)->sel(j));
	}
      }

      addM->setDef(def);
      
	      
      RunGenerators rg;
      rg.runOnNamespace(g);

      Type* t = addM->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph g;
      buildOrderedGraph(addM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, addM);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      string outFile = "./gencode/mat2_3_add.c";
      int s = compileCodeAndRun(topoOrder,
				g,
				addM,
				"./gencode/mat2_3_add",
				"./gencode/test_mat2_3_add.c");

      REQUIRE(s == 0);
    }

    SECTION("Equality comparison on 54 bits") {
      uint n = 54;
  
      Generator* eq = c->getGenerator("coreir.eq");

      Type* eqType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Bit() }
	});

      Module* eqM = g->newModuleDecl("equality_test", eqType);

      ModuleDef* def = eqM->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* eq0 = def->addInstance("eq0", eq, {{"width", c->argInt(n)}});

      def->connect("self.A.0", "eq0.in0");
      def->connect("self.A.1", "eq0.in1");
      def->connect(eq0->sel("out"), self->sel("out"));

      eqM->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(eqM, g);

      deque<vdisc> topoOrder = topologicalSort(g);


      auto str = printCode(topoOrder, g, eqM);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      compileCode(str, "./gencode/eq54.c");
    }

    SECTION("sle on 7 bits") {
      uint n = 7;
  
      Generator* sle = c->getGenerator("coreir.sle");

      Type* sleType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Bit() }
	});

      Module* sleM = g->newModuleDecl("sle_test", sleType);

      ModuleDef* def = sleM->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* sle0 = def->addInstance("sle0", sle, {{"width", c->argInt(n)}});

      def->connect("self.A.0", "sle0.in0");
      def->connect("self.A.1", "sle0.in1");
      def->connect(sle0->sel("out"), self->sel("out"));

      sleM->setDef(def);

      RunGenerators rg;
      rg.runOnNamespace(g);

      NGraph g;
      buildOrderedGraph(sleM, g);

      deque<vdisc> topoOrder = topologicalSort(g);


      auto str = printCode(topoOrder, g, sleM);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      int s = compileCodeAndRun(topoOrder,
				g,
				sleM,
				"./gencode/sle7", "./gencode/test_sle7.c");
      REQUIRE(s == 0);

    }
    
    deleteContext(c);

  }

  bool splitNodeEdgesCorrect(const NGraph& g) {

    cout << "Edges" << endl;

    for (auto& ed : g.getEdges()) {
      Conn c = getConn(g, ed);

      cout << (c.first).toString() << " ---> " << (c.second).toString() << endl;

      // Either the first edge is not a register or it is not a receiver
      Wireable* fstParent = toSelect(*(c.first.getWire())).getParent();
      bool notRec = !isRegisterInstance(fstParent) ||
	(c.first.isSequential && !(c.first.isReceiver));

      if (!notRec) { return false; }

      // Either the second edge is not a register or it is a reciver
      Wireable* sndParent = toSelect(*(c.second.getWire())).getParent();
      bool isRec = !isRegisterInstance(sndParent) ||
	(c.second.isSequential && c.second.isReceiver);

      if (!isRec) { return false; }
    }

    return true;

  }

  TEST_CASE("Sequential logic") {

    Context* c = newContext();

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

      def->addInstance("r", "coreir.reg", {{"width", c->argInt(n)}, {"en", c->argBool(true)}});

      def->connect("self.en", "r.en");
      def->connect("self.clk", "r.clk");
      def->connect("self.a", "r.in");
      def->connect("r.out", "self.out");

      rg->setDef(def);

      RunGenerators runGen;
      runGen.runOnNamespace(c->getGlobal());

      NGraph g;
      buildOrderedGraph(rg, g);

      SECTION("Checking number of vertices") {
      	REQUIRE(numVertices(g) == 6);
      }

      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      REQUIRE(splitNodeEdgesCorrect(g));

      auto str = printCode(topoOrder, g, rg);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      SECTION("Compile and run") {      
	string outFile = "./gencode/reg5";

	int s = compileCodeAndRun(topoOrder,
				  g,
				  rg,
				  outFile,
				  "gencode/test_reg5.c");

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

      Args wArg({{"width",c->argInt(16)}});
      def->addInstance("ai","coreir.add",wArg); // using <namespace>.<module> notation 
      def->addInstance("ci","coreir.const",wArg,{{"value",c->argInt(1)}});

      //Reg has default arguments. en/clr/rst are False by default. Init is also 0 by default
      def->addInstance("ri","coreir.reg",{{"width",c->argInt(16)},{"en",c->argBool(true)}});
    
      //Connections
      def->connect("self.clk","ri.clk");
      def->connect("self.en","ri.en");
      def->connect("ci.out","ai.in0");
      def->connect("ai.out","ri.in");
      def->connect("ri.out","ai.in1");
      def->connect("ri.out","self.out");

      counter->setDef(def);
      counter->print();
  
      RunGenerators rg;
      rg.runOnNamespace(c->getGlobal());

      NGraph g;
      buildOrderedGraph(counter, g);

      SECTION("Checking number of vertices") {
      	// clk, en, out, ai, ci, ri_in, ri_out
      	REQUIRE(numVertices(g) == 7);
      }

      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      REQUIRE(splitNodeEdgesCorrect(g));

      auto str = printCode(topoOrder, g, counter);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      SECTION("Compile and run") {      
	string outFile = "./gencode/counter";

	int s = compileCodeAndRun(topoOrder,
				  g,
				  counter,
				  outFile,
				  "./gencode/test_counter.c");

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
      Args wArg({{"width",c->argInt(16)}});

      def->addInstance("ai", "coreir.add", wArg);
      def->addInstance("r0","coreir.reg",{{"width",c->argInt(16)},{"en",c->argBool(true)}});
      def->addInstance("r1","coreir.reg",{{"width",c->argInt(16)},{"en",c->argBool(true)}});
      def->addInstance("r2","coreir.reg",{{"width",c->argInt(16)},{"en",c->argBool(true)}});
    
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
  
      RunGenerators rg;
      rg.runOnNamespace(c->getGlobal());

      NGraph g;
      buildOrderedGraph(regChain, g);

      SECTION("Checking number of vertices") {
	REQUIRE(splitNodeEdgesCorrect(g));	

      	// clk, en, ap, bp, out, ai, r0_in, r0_out, r1_in, r1_out, r2_in, r2_out
      	REQUIRE(numVertices(g) == 12);
      }



      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      auto str = printCode(topoOrder, g, regChain);
      cout << "CODE STRING" << endl;
      cout << str << endl;

      SECTION("Compile and run") {      
	string outFile = "./gencode/register_chain.c";
	int s = compileCode(str, outFile);

	REQUIRE(s == 0);

      }
      
    }

    SECTION("Register without enable") {

      Type* regChainType = c->Record({
	  {"a", c->BitIn()->Arr(8)},
	    {"cout",c->Bit()->Arr(8)},
	      {"clk",c->Named("coreir.clkIn")},
		});

      Module* regChain = c->getGlobal()->newModuleDecl("regChain", regChainType);
      ModuleDef* def = regChain->newModuleDef();

      def->addInstance("r0","coreir.reg",{{"width",c->argInt(8)},{"en",c->argBool(false)}});
    
      //Connections
      def->connect("self.clk", "r0.clk");
      def->connect("self.a", "r0.in");
      def->connect("r0.out","self.cout");

      regChain->setDef(def);
  
      RunGenerators rg;
      rg.runOnNamespace(c->getGlobal());

      NGraph g;
      buildOrderedGraph(regChain, g);

      SECTION("Checking number of vertices") {
	REQUIRE(splitNodeEdgesCorrect(g));	

      	REQUIRE(numVertices(g) == 5);
      }



      cout << "About to topological sort" << endl;
      deque<vdisc> topoOrder = topologicalSort(g);
      cout << "Done topological sorting" << endl;

      auto str = printCode(topoOrder, g, regChain);
      cout << "CODE STRING" << endl;
      cout << str << endl;
      
      SECTION("Compile and run") {
	string outFile = "./gencode/register_no_enable.c";
	int s = compileCode(str, outFile);

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
				       "coreir.reg",
				       {{"width",c->argInt(n)},
					   {"en",c->argBool(false)}});

	def->connect(self->sel("clkArr")->sel(i), r->sel("clk"));
	def->connect(self->sel("a")->sel(i), r->sel("in"));

	def->connect(r->sel("out"), self->sel("b")->sel(i));
      }

      clkArr->setDef(def);


      RunGenerators rg;
      rg.runOnNamespace(c->getGlobal());

      cout << "Building graph" << endl;

      NGraph g;
      buildOrderedGraph(clkArr, g);

      cout << "Done building graph" << endl;

      SECTION("Checking number of vertices") {
	REQUIRE(splitNodeEdgesCorrect(g));	

      	REQUIRE(numVertices(g) == 9);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      auto str = printCode(topoOrder, g, clkArr);
      cout << "CODE STRING" << endl;
      cout << str << endl;
      
      SECTION("Compile and run") {
	string outFile = "./gencode/clock_array.c";
	int s = compileCode(str, outFile);

	REQUIRE(s == 0);
      }
      
    }
    
    deleteContext(c);

  }
  
}
