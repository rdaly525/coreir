#include "catch.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/libs/commonlib.h"

#include "fuzzing.hpp"

#include "coreir/simulator/output.h"
#include "coreir/simulator/simulator.h"
#include "coreir/simulator/utils.h"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  void colorAdd4Tree(NGraph& g) {
    for (auto& vd : g.getVerts()) {
      WireNode wd = g.getNode(vd);


      Wireable* w = wd.getWire();
      cout << "VD " << vd << " = " << w->toString() << endl;

      if (isSelect(w)) {
	string ss = toSelect(w)->getSelStr();

	if (ss == "in0" || ss == "in1") {
	  wd.setThreadNo(0);
	} else if (ss == "in2" || ss == "in3") {
	  wd.setThreadNo(1);
	} else if (ss == "out") {
	  wd.setThreadNo(3);
	} else {
	  assert(false);
	}
      } else {
	if (w->toString() == "add00") {
	  wd.setThreadNo(0);
	} else if (w->toString() == "add01") {
	  wd.setThreadNo(1);
	} else if (w->toString() == "add1") {
	  wd.setThreadNo(2);
	} else {
	  assert(false);
	}
      }

      g.addVertLabel(vd, wd);
    }
  }

  // Problem: Need to handle nodes that represent arrays
  void colorConnectedComponents(NGraph& g) {
    vector<vdisc> inVerts = vertsWithNoIncomingEdge(g);

    cout << "inVerts size = " << inVerts.size() << endl;

    int currentThread = 0;

    for (auto& inVert : inVerts) {

      vector<vdisc> s{inVert};

      while (s.size() > 0) {
	vdisc vd = s.back();

	WireNode w = g.getNode(vd);
	w.setThreadNo(currentThread);

	g.addVertLabel(vd, w);

	s.pop_back();

	for (auto ed : g.outEdges(vd)) {
	  vdisc input = g.target(ed);
	  s.push_back(input);
	}
      
      }

      currentThread++;
    }
  }

  TEST_CASE("Combinational logic simulation") {

    // New context
    Context* c = newContext();
  
    Namespace* g = c->getGlobal();

    SECTION("Load add with cin / cout from json") {
      if (!loadFromFile(c, "test_add_cin_two.json")) {
	cout << "Could not Load from json!!" << endl;
	c->die();
      }

      Module* m = c->getModule("global.Add4_cin");

      c->runPasses({"rungenerators"});

      NGraph gr;
      buildOrderedGraph(m, gr);
      deque<vdisc> topoOrder = topologicalSort(gr);

      SECTION("Compile and run") {
	int s = compileCode(topoOrder, gr, m, "./gencode/", "add_cin_two");

	REQUIRE(s == 0);
      }

    }
	       

    SECTION("16 bit add with carry out only") {
      uint n = 16;
  
      Generator* add2 = c->getGenerator("mantle.add");

      // Define Add4 Module
      Type* add4Type = c->Record({
    	  {"in",c->Array(2,c->Array(n,c->BitIn()))},
    	    {"out",c->Array(n,c->Bit())},
	      {"cout", c->Bit()}
    	});

      Module* add4_n = g->newModuleDecl("Add4",add4Type);
      ModuleDef* def = add4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* add0 = def->addInstance("add0",add2,{{"width", Const::make(c, n)}, {"has_cin", Const::make(c, false)}, {"has_cout", Const::make(c, true)}});
    
      def->connect(self->sel("in")->sel(0), add0->sel("in0"));
      def->connect(self->sel("in")->sel(1), add0->sel("in1"));
      def->connect(add0->sel("out"), self->sel("out"));
      def->connect(add0->sel("cout"), self->sel("cout"));
      add4_n->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph gr;
      buildOrderedGraph(add4_n, gr);
      deque<vdisc> topoOrder = topologicalSort(gr);

      SECTION("Compile and run") {
	int s = compileCodeAndRun(topoOrder,
				  gr,
				  add4_n,
				  "./gencode/",
				  "add_cout_16",
				  "test_add_cout_16.cpp");

    	REQUIRE(s == 0);
      }

    }
    
    SECTION("31 bit add with carry in and carry out") {
      uint n = 31;
  
      Generator* add2 = c->getGenerator("mantle.add");

      // Define Add4 Module
      Type* add4Type = c->Record({
    	  {"in",c->Array(2,c->Array(n,c->BitIn()))},
    	    {"out",c->Array(n,c->Bit())},
    	      {"cin", c->BitIn()},
    		{"cout", c->Bit()}
    	});

      Module* add4_n = g->newModuleDecl("Add4",add4Type);
      ModuleDef* def = add4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* add0 = def->addInstance("add0",add2,{{"width", Const::make(c, n)}, {"has_cin", Const::make(c, true)}, {"has_cout", Const::make(c, true)}});
    
      def->connect(self->sel("in")->sel(0), add0->sel("in0"));
      def->connect(self->sel("in")->sel(1), add0->sel("in1"));
      def->connect(self->sel("cin"), add0->sel("cin"));
      def->connect(add0->sel("out"), self->sel("out"));
      def->connect(add0->sel("cout"), self->sel("cout"));
      add4_n->setDef(def);

      c->runPasses({"rungenerators"});
      NGraph gr;
      buildOrderedGraph(add4_n, gr);
      deque<vdisc> topoOrder = topologicalSort(gr);

      SECTION("Compile and run") {
	int s = compileCodeAndRun(topoOrder,
				  gr,
				  add4_n,
				  "./gencode/",
				  "add_cin_cout",
				  "test_add_cin_cout.cpp");

    	REQUIRE(s == 0);
      }

    }

    SECTION("32 bit add with carry in and carry out") {
      uint n = 32;
  
      Generator* add2 = c->getGenerator("mantle.add");

      // Define Add4 Module
      Type* add4Type = c->Record({
    	  {"in",c->Array(2,c->Array(n,c->BitIn()))},
    	    {"out",c->Array(n,c->Bit())},
    	      {"cin", c->BitIn()},
    		{"cout", c->Bit()}
    	});

      Module* add4_n = g->newModuleDecl("Add4",add4Type);
      ModuleDef* def = add4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* add0 = def->addInstance("add0",add2,{{"width", Const::make(c, n)}, {"has_cin", Const::make(c, true)}, {"has_cout", Const::make(c, true)}});
    
      def->connect(self->sel("in")->sel(0), add0->sel("in0"));
      def->connect(self->sel("in")->sel(1), add0->sel("in1"));
      def->connect(self->sel("cin"), add0->sel("cin"));
      def->connect(add0->sel("out"), self->sel("out"));
      def->connect(add0->sel("cout"), self->sel("cout"));
      add4_n->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph gr;
      buildOrderedGraph(add4_n, gr);
      deque<vdisc> topoOrder = topologicalSort(gr);

      SECTION("Compile and run") {
	int s = compileCodeAndRun(topoOrder,
				  gr,
				  add4_n,
				  "./gencode/",
				  "add_cin_cout_32",
				  "test_add_cin_cout_32.cpp");

    	REQUIRE(s == 0);
      }

    }
    
    SECTION("32 bit add 4") {

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
      Wireable* add_00 = def->addInstance("add00",add2,{{"width", Const::make(c,n)}});
      Wireable* add_01 = def->addInstance("add01",add2,{{"width", Const::make(c,n)}});
      Wireable* add_1 = def->addInstance("add1",add2,{{"width", Const::make(c,n)}});
    
      def->connect(self->sel("in0"), add_00->sel("in0"));
      def->connect(self->sel("in1"), add_00->sel("in1"));
      def->connect(self->sel("in2"), add_01->sel("in0"));
      def->connect(self->sel("in3"), add_01->sel("in1"));

      def->connect(add_00->sel("out"),add_1->sel("in0"));
      def->connect(add_01->sel("out"),add_1->sel("in1"));

      def->connect(add_1->sel("out"),self->sel("out"));
      add4_n->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph gr;
      buildOrderedGraph(add4_n, gr);
      deque<vdisc> topoOrder = topologicalSort(gr);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(gr) == 8);
      }

      SECTION("Checking mask elimination") {
      	eliminateMasks(topoOrder, gr);

      	REQUIRE(numMasksNeeded(gr) == 3);
      }

      SECTION("Compile and run") {
	int s = compileCode(topoOrder, gr, add4_n, "./gencode/", "add4");

	saveToFile(g, "add4.json");

	REQUIRE(s == 0);
      }

      // SECTION("Compile multithreaded code") {
      //   cout << "32 bit add 4 multithreaded" << endl;
      //   colorAdd4Tree(gr);

      //   SECTION("Checking thread graph properties") {
      //     ThreadGraph tg = buildThreadGraph(gr);

      //     REQUIRE(tg.getVerts().size() == 4);
      //     REQUIRE(tg.getEdges().size() == 3);
      //   }

      //   deque<vdisc> topoOrder = topologicalSort(gr);

      //   for (auto& vd : topoOrder) {
      //     WireNode wd = gr.getNode(vd);
      //     cout << "Node " << vd << " has thread number = " << wd.getThreadNo() << endl;
      //   }

      //   int s = compileCodeAndRun(topoOrder,
      //   			  gr,
      //   			  add4_n,
      //   			  "./gencode/",
      //   			  "add4_parallel",
      //   			  "test_add4_parallel.cpp");
      //   REQUIRE(s == 0);
	
      // }

    }

    SECTION("6 bit signed remainder 3 operations") {
      uint n = 6;
  
      Generator* srem2 = c->getGenerator("coreir.srem");

      // Define Srem4 Module
      Type* srem4Type = c->Record({
	  {"in",c->Array(3, c->Array(n,c->BitIn()))},
	    {"out",c->Array(n, c->Bit())}
	});

      Module* srem4_n = g->newModuleDecl("Srem4", srem4Type);
      ModuleDef* def = srem4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* srem_00 = def->addInstance("srem00", srem2, {{"width", Const::make(c,n)}});
      Wireable* srem_01 = def->addInstance("srem01", srem2, {{"width", Const::make(c,n)}});
      Wireable* srem_1 = def->addInstance("srem1", srem2, {{"width", Const::make(c,n)}});

      def->connect(self->sel("in")->sel(0),srem_00->sel("in0"));
      def->connect(self->sel("in")->sel(1),srem_00->sel("in1"));

      def->connect(self->sel("in")->sel(2),srem_01->sel("in0"));
      def->connect(srem_00->sel("out"), srem_01->sel("in1"));

      def->connect(srem_00->sel("out"),srem_1->sel("in0"));
      def->connect(srem_01->sel("out"),srem_1->sel("in1"));

      def->connect(srem_1->sel("out"),self->sel("out"));
      srem4_n->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph gr;
      buildOrderedGraph(srem4_n, gr);
      
      deque<vdisc> topoOrder = topologicalSort(gr);

      int s = compileCodeAndRun(topoOrder,
				gr,
				srem4_n,
				"./gencode/",
				"srem4",
				"test_srem4.cpp");

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
      Wireable* sub_00 = def->addInstance("sub00",sub2,{{"width", Const::make(c,n)}});
      Wireable* sub_01 = def->addInstance("sub01",sub2,{{"width", Const::make(c,n)}});
      Wireable* sub_1 = def->addInstance("sub1",sub2,{{"width", Const::make(c,n)}});
    
      def->connect(self->sel("in")->sel(0), sub_00->sel("in0"));
      def->connect(self->sel("in")->sel(1), sub_00->sel("in1"));
      def->connect(self->sel("in")->sel(2), sub_01->sel("in0"));
      def->connect(self->sel("in")->sel(3), sub_01->sel("in1"));

      def->connect(sub_00->sel("out"),sub_1->sel("in0"));
      def->connect(sub_01->sel("out"),sub_1->sel("in1"));

      def->connect(sub_1->sel("out"),self->sel("out"));
      sub4_n->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(sub4_n, g);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(g) == 5);
      }
      
      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {
	int s = compileCode(topoOrder, g, sub4_n, "./gencode/", "sub4");

	REQUIRE(s == 0);
      }
      
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
      Wireable* mul = def->addInstance("mul1", mul2, {{"width", Const::make(c,n)}});
    
      def->connect(self->sel("in")->sel(0), mul->sel("in0"));
      def->connect(self->sel("in")->sel(1), mul->sel("in1"));

      def->connect(mul->sel("out"), self->sel("out"));
      mul_n->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(mul_n, g);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(g) == 3);
      }
      
      deque<vdisc> topoOrder = topologicalSort(g);

      int s = compileCode(topoOrder, g, mul_n, "./gencode/", "mul2");
      REQUIRE(s == 0);

    }

    SECTION("And then add, mask removal test") {
      uint n = 50;

      Generator* andG = c->getGenerator("coreir.and");
      Generator* addG = c->getGenerator("coreir.add");

      Type* cType = c->Record({
	  {"a", c->Array(n, c->BitIn())},
	    {"b", c->Array(n, c->BitIn())},
	      {"c", c->Array(n, c->BitIn())},
		{"out", c->Array(n, c->Bit())}
	});

      Module* cM = g->newModuleDecl("addAnd", cType);
      ModuleDef* def = cM->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* and0 = def->addInstance("and0", andG, {{"width", Const::make(c,n)}});
      Wireable* add0 = def->addInstance("add0", addG, {{"width", Const::make(c,n)}});


      def->connect(self->sel("a"), add0->sel("in0"));
      def->connect(self->sel("b"), add0->sel("in1"));

      def->connect(add0->sel("out"), and0->sel("in0"));
      def->connect(self->sel("c"), and0->sel("in1"));

      def->connect(and0->sel("out"), self->sel("out"));

      cM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(cM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Checking mask elimination") {
      	eliminateMasks(topoOrder, g);

      	REQUIRE(numMasksNeeded(g) == 1);
      }
      
    }

    SECTION("One 37 bit and") {
      uint n = 37;

      Generator* andG = c->getGenerator("coreir.and");

      Type* andType = c->Record({
	  {"input", c->Array(2, c->Array(n, c->BitIn()))},
	    {"output", c->Array(n, c->Bit())}
	});

      Module* andM = g->newModuleDecl("and37", andType);

      ModuleDef* def = andM->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* and0 = def->addInstance("and0", andG, {{"width", Const::make(c,n)}});

      def->connect("self.input.0", "and0.in0");
      def->connect("self.input.1", "and0.in1");
      def->connect("and0.out", "self.output");

      andM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(andM, g);

      SECTION("Checking graph size") {
      	REQUIRE(numVertices(g) == 3);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      eliminateMasks(topoOrder, g);

      REQUIRE(numMasksNeeded(g) == 0);

      SECTION("Compiling code") {

	string outFile = "./gencode/and37.cpp";

	int s = compileCodeAndRun(topoOrder,
				  g,
				  andM,
				  "./gencode/",
				  "and37",
				  "test_and37.cpp");

	cout << "Test result = " << s << endl;

	REQUIRE(s == 0);
      }
      
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
      Wireable* add0 = def->addInstance("add0", addG, {{"width", Const::make(c,n)}});

      def->connect("self.input.0", "add0.in0");
      def->connect("self.input.1", "add0.in1");
      def->connect("add0.out", "self.output");

      addM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(addM, g);

      SECTION("Checking graph size") {
      	REQUIRE(numVertices(g) == 3);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "add63";
      int s = compileCodeAndRun(topoOrder,
				g,
				addM,
				"./gencode/",
				outFile,
				"test_add63.cpp");

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
      Wireable* neg0 = def->addInstance("neg0", neg, {{"width", Const::make(c,n)}});

      def->connect(self->sel("A"), neg0->sel("in"));

      def->connect(neg0->sel("out"), self->sel("res"));

      neg_n->setDef(def);

      c->runPasses({"rungenerators"});

      Type* t = neg_n->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph gr;
      buildOrderedGraph(neg_n, gr);
      deque<vdisc> topoOrder = topologicalSort(gr);

      SECTION("Checking mask elimination") {
      	eliminateMasks(topoOrder, gr); // Set highBitsDirty

      	REQUIRE(numMasksNeeded(gr) == 1);
      }

      SECTION("Compiling code") {

	string outFile = "neg2";
	int s = compileCodeAndRun(topoOrder,
				  gr,
				  neg_n,
				  "./gencode/",
				  outFile,
				  "test_neg2.cpp");

	REQUIRE(s == 0);

      }

      
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
      Wireable* neg0 = def->addInstance("neg0", neg, {{"width", Const::make(c,n)}});

      def->connect(self->sel("A"), neg0->sel("in"));

      def->connect(neg0->sel("out"), self->sel("res"));

      neg_n->setDef(def);

      c->runPasses({"rungenerators"});

      Type* t = neg_n->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph g;
      buildOrderedGraph(neg_n, g);

      SECTION("Checking graph size") {
      	REQUIRE(numVertices(g) == 3);
      }

      deque<vdisc> topoOrder = topologicalSort(g);

      int s = compileCode(topoOrder, g, neg_n, "./gencode/", "neg16");
      REQUIRE(s == 0);
      
    }
    
    SECTION("Two 16 bit nots") {
      uint n = 16;
  
      Generator* neg = c->getGenerator("coreir.not");

      Type* neg2Type = c->Record({
	  {"in0",    c->Array(n,c->BitIn())},
	    {"in1",    c->Array(n,c->BitIn())},
	      {"out0", c->Array(n,c->Bit())},
		{"out1", c->Array(n,c->Bit())},
	});

      Module* neg_n = g->newModuleDecl("two_negs", neg2Type);

      ModuleDef* def = neg_n->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* neg0 = def->addInstance("neg0", neg, {{"width", Const::make(c,n)}});
      Wireable* neg1 = def->addInstance("neg1", neg, {{"width", Const::make(c,n)}});

      def->connect(self->sel("in0"), neg0->sel("in"));
      def->connect(self->sel("in1"), neg1->sel("in"));

      def->connect(neg0->sel("out"), self->sel("out0"));
      def->connect(neg1->sel("out"), self->sel("out1"));

      neg_n->setDef(def);

      c->runPasses({"rungenerators"});

      Type* t = neg_n->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph g;
      buildOrderedGraph(neg_n, g);

      SECTION("Checking graph size") {
	REQUIRE(numVertices(g) == 6);
      }

      SECTION("Printing single threaded code") {
	deque<vdisc> topoOrder = topologicalSort(g);
	int s = compileCode(topoOrder, g, neg_n, "./gencode/", "two_negs");
	REQUIRE(s == 0);
      }

      SECTION("Printing multithreaded code") {
	colorConnectedComponents(g);
	deque<vdisc> topoOrder = topologicalSort(g);

	for (auto& vd : topoOrder) {
	  WireNode wd = g.getNode(vd);
	  cout << "Node " << vd << " has thread number = " << wd.getThreadNo() << endl;
	}

	int s = compileCode(topoOrder, g, neg_n, "./gencode/", "two_negs_parallel");
	REQUIRE(s == 0);
	
      }

      
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
	  Wireable* addInst = def->addInstance(str, add, {{"width", Const::make(c,n)}});

	  def->connect(self->sel("A")->sel(i)->sel(j), addInst->sel("in0"));
	  def->connect(self->sel("B")->sel(i)->sel(j), addInst->sel("in1"));

	  def->connect(addInst->sel("out"), self->sel("out")->sel(i)->sel(j));
	}
      }

      addM->setDef(def);
      
      c->runPasses({"rungenerators"});

      Type* t = addM->getType();
      cout << "Module type = " << t->toString() << endl;
      
      NGraph g;
      buildOrderedGraph(addM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "./gencode/mat2_3_add.cpp";
      int s = compileCodeAndRun(topoOrder,
				g,
				addM,
				"./gencode/",
				"mat2_3_add",
				"test_mat2_3_add.cpp");

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
      Wireable* eq0 = def->addInstance("eq0", eq, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "eq0.in0");
      def->connect("self.A.1", "eq0.in1");
      def->connect(eq0->sel("out"), self->sel("out"));

      eqM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(eqM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      int s = compileCode(topoOrder, g, eqM, "./gencode/", "eq54");
      REQUIRE(s == 0);
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
      Wireable* sle0 = def->addInstance("sle0", sle, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "sle0.in0");
      def->connect("self.A.1", "sle0.in1");
      def->connect(sle0->sel("out"), self->sel("out"));

      sleM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(sleM, g);

      deque<vdisc> topoOrder = topologicalSort(g);
      eliminateMasks(topoOrder, g);

      REQUIRE(numMasksNeeded(g) == 0);


      int s = compileCodeAndRun(topoOrder,
				g,
				sleM,
				"./gencode/",
				"sle7",
				"test_sle7.cpp");
      REQUIRE(s == 0);

    }

    SECTION("gt on 16 bits") {
      uint n = 16;
  
      Generator* ugt = c->getGenerator("coreir.ugt");

      Type* ugtType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Bit() }
	});

      Module* ugtM = g->newModuleDecl("ugt_test", ugtType);

      ModuleDef* def = ugtM->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* ugt0 = def->addInstance("ugt0", ugt, {{"width", Const::make(c, n)}});

      def->connect("self.A.0", "ugt0.in0");
      def->connect("self.A.1", "ugt0.in1");
      def->connect(ugt0->sel("out"), self->sel("out"));

      ugtM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(ugtM, g);

      deque<vdisc> topoOrder = topologicalSort(g);
      eliminateMasks(topoOrder, g);

      REQUIRE(numMasksNeeded(g) == 0);

      int s = compileCodeAndRun(topoOrder,
				g,
				ugtM,
				"./gencode/",
				"ugt16",
				"test_ugt16.cpp");
      REQUIRE(s == 0);

    }
    
    SECTION("Multiplexer test") {
      uint n = 8;
  
      Type* muxType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"sel", c->BitIn()},
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* muxM = g->newModuleDecl("muxM", muxType);
      ModuleDef* def = muxM->newModuleDef();

      Generator* mux = c->getGenerator("coreir.mux");

      Wireable* self = def->sel("self");
      Wireable* mux0 = def->addInstance("mux0", mux, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "mux0.in0");
      def->connect("self.A.1", "mux0.in1");
      def->connect("self.sel", "mux0.sel");
      def->connect(mux0->sel("out"), self->sel("out"));

      muxM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(muxM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "mux8";

      int s = compileCodeAndRun(topoOrder,
				g,
				muxM,
				"./gencode/",
				outFile,
				"test_mux8.cpp");

      REQUIRE(s == 0);
      
    }

    SECTION("32 bit dshl test") {
      uint n = 32;
  
      Type* dshlType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* dshlM = g->newModuleDecl("dshlM", dshlType);
      ModuleDef* def = dshlM->newModuleDef();

      Generator* dshl = c->getGenerator("coreir.shl");

      Wireable* self = def->sel("self");
      Wireable* dshl0 = def->addInstance("dshl0", dshl, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "dshl0.in0");
      def->connect("self.A.1", "dshl0.in1");
      def->connect(dshl0->sel("out"), self->sel("out"));

      dshlM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(dshlM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "dshl32";

      int s = compileCodeAndRun(topoOrder,
				g,
				dshlM,
				"./gencode/",
				outFile,
				"test_dshl32.cpp");

      REQUIRE(s == 0);
      
    }

    SECTION("Multiply then shift 16 bit") {
      uint n = 16;

      Type* dashrType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* dashrM = g->newModuleDecl("dashrM", dashrType);
      ModuleDef* def = dashrM->newModuleDef();

      Generator* dashr = c->getGenerator("coreir.ashr");

      Wireable* self = def->sel("self");
      Wireable* dashr0 =
        def->addInstance("dashr0", dashr, {{"width", Const::make(c,n)}});
      auto mul0 =
        def->addInstance("mul0", "coreir.mul", {{"width", Const::make(c, n)}});
      auto c0 =
        def->addInstance("four",
                         "coreir.const",
                         {{"width", Const::make(c, n)}},
                         {{"value", Const::make(c, BitVector(n, 4))}});


      def->connect("self.A.0", "mul0.in0");
      def->connect("self.A.1", "mul0.in1");
      def->connect("four.out", "dashr0.in1");
      def->connect("mul0.out", "dashr0.in0");
      def->connect(dashr0->sel("out"), self->sel("out"));

      dashrM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(dashrM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "multiply_shift_16";

      int s = compileCodeAndRun(topoOrder,
				g,
				dashrM,
				"./gencode/",
				outFile,
				"test_multiply_shift_16.cpp");

      REQUIRE(s == 0);
      
    }
    

    SECTION("60 bit dashr test") {
      uint n = 60;
  
      Type* dashrType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* dashrM = g->newModuleDecl("dashrM", dashrType);
      ModuleDef* def = dashrM->newModuleDef();

      Generator* dashr = c->getGenerator("coreir.ashr");

      Wireable* self = def->sel("self");
      Wireable* dashr0 = def->addInstance("dashr0", dashr, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "dashr0.in0");
      def->connect("self.A.1", "dashr0.in1");
      def->connect(dashr0->sel("out"), self->sel("out"));

      dashrM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(dashrM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "dashr60";

      int s = compileCodeAndRun(topoOrder,
				g,
				dashrM,
				"./gencode/",
				outFile,
				"test_dashr60.cpp");

      REQUIRE(s == 0);
      
    }

    SECTION("5 bit dlshr test") {
      uint n = 5;
  
      Type* dlshrType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* dlshrM = g->newModuleDecl("dlshrM", dlshrType);
      ModuleDef* def = dlshrM->newModuleDef();

      Generator* dlshr = c->getGenerator("coreir.lshr");

      Wireable* self = def->sel("self");
      Wireable* dlshr0 = def->addInstance("dlshr0", dlshr, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "dlshr0.in0");
      def->connect("self.A.1", "dlshr0.in1");
      def->connect(dlshr0->sel("out"), self->sel("out"));

      dlshrM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(dlshrM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "dlshr5";

      int s = compileCodeAndRun(topoOrder,
				g,
				dlshrM,
				"./gencode/",
				outFile,
				"test_dlshr5.cpp");

      REQUIRE(s == 0);
    }

    SECTION("Unsigned 27 bit division") {
      uint n = 27;
  
      Type* udivType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* udivM = g->newModuleDecl("udivM", udivType);
      ModuleDef* def = udivM->newModuleDef();

      Generator* udiv = c->getGenerator("coreir.udiv");

      Wireable* self = def->sel("self");
      Wireable* udiv0 = def->addInstance("udiv0", udiv, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "udiv0.in0");
      def->connect("self.A.1", "udiv0.in1");
      def->connect(udiv0->sel("out"), self->sel("out"));

      udivM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(udivM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "udiv27";

      int s = compileCodeAndRun(topoOrder,
				g,
				udivM,
				"./gencode/",
				outFile,
				"test_udiv27.cpp");

      REQUIRE(s == 0);
      
    }

    SECTION("Unsigned 13 bit remainder") {
      uint n = 13;
  
      Type* uremType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* uremM = g->newModuleDecl("uremM", uremType);
      ModuleDef* def = uremM->newModuleDef();

      Generator* urem = c->getGenerator("coreir.urem");

      Wireable* self = def->sel("self");
      Wireable* urem0 = def->addInstance("urem0", urem, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "urem0.in0");
      def->connect("self.A.1", "urem0.in1");
      def->connect(urem0->sel("out"), self->sel("out"));

      uremM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(uremM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "urem13";

      int s = compileCodeAndRun(topoOrder,
				g,
				uremM,
				"./gencode/",
				outFile,
				"test_urem13.cpp");

      REQUIRE(s == 0);
      
    }

    SECTION("Signed 5 bit remainder") {
      uint n = 5;
  
      Type* sremType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* sremM = g->newModuleDecl("sremM", sremType);
      ModuleDef* def = sremM->newModuleDef();

      Generator* srem = c->getGenerator("coreir.srem");

      Wireable* self = def->sel("self");
      Wireable* srem0 = def->addInstance("srem0", srem, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "srem0.in0");
      def->connect("self.A.1", "srem0.in1");
      def->connect(srem0->sel("out"), self->sel("out"));

      sremM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(sremM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "srem5";

      int s = compileCodeAndRun(topoOrder,
				g,
				sremM,
				"./gencode/",
				outFile,
				"test_srem5.cpp");

      REQUIRE(s == 0);
      
    }

    SECTION("Signed 5 bit division") {
      uint n = 5;
  
      Type* sdivType = c->Record({
	  {"A",    c->Array(2, c->Array(n, c->BitIn())) },
	    {"out", c->Array(n, c->Bit()) }
	});

      Module* sdivM = g->newModuleDecl("sdivM", sdivType);
      ModuleDef* def = sdivM->newModuleDef();

      Generator* sdiv = c->getGenerator("coreir.sdiv");

      Wireable* self = def->sel("self");
      Wireable* sdiv0 = def->addInstance("sdiv0", sdiv, {{"width", Const::make(c,n)}});

      def->connect("self.A.0", "sdiv0.in0");
      def->connect("self.A.1", "sdiv0.in1");
      def->connect(sdiv0->sel("out"), self->sel("out"));

      sdivM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(sdivM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "sdiv5";

      int s = compileCodeAndRun(topoOrder,
				g,
				sdivM,
				"./gencode/",
				outFile,
				"test_sdiv5.cpp");

      REQUIRE(s == 0);
      
    }

    SECTION("38 bit orr") {
      uint n = 38;
  
      Type* orrType = c->Record({
	  {"A",    c->Array(n, c->BitIn()) },
	    {"out", c->Bit() }
	});

      Module* orrM = g->newModuleDecl("orrM", orrType);
      ModuleDef* def = orrM->newModuleDef();

      Generator* orr = c->getGenerator("coreir.orr");

      Wireable* self = def->sel("self");
      Wireable* orr0 = def->addInstance("orr0", orr, {{"width", Const::make(c,n)}});

      def->connect("self.A", "orr0.in");
      def->connect(orr0->sel("out"), self->sel("out"));

      orrM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(orrM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "orr38";

      int s = compileCodeAndRun(topoOrder,
				g,
				orrM,
				"./gencode/",
				outFile,
				"test_orr38.cpp");

      REQUIRE(s == 0);
    }

    SECTION("59 bit andr") {
      uint n = 59;
  
      Type* andrType = c->Record({
	  {"A",    c->Array(n, c->BitIn()) },
	    {"out", c->Bit() }
	});

      Module* andrM = g->newModuleDecl("andrM", andrType);
      ModuleDef* def = andrM->newModuleDef();

      Generator* andr = c->getGenerator("coreir.andr");

      Wireable* self = def->sel("self");
      Wireable* andr0 = def->addInstance("andr0", andr, {{"width", Const::make(c,n)}});

      def->connect("self.A", "andr0.in");
      def->connect(andr0->sel("out"), self->sel("out"));

      andrM->setDef(def);

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(andrM, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      string outFile = "andr59";

      int s = compileCodeAndRun(topoOrder,
				g,
				andrM,
				"./gencode/",
				outFile,
				"test_andr59.cpp");

      REQUIRE(s == 0);
    }
    
    SECTION("Circuit with module references") {

      cout << "loading" << endl;
      if (!loadFromFile(c, "main.json")) {
	cout << "Could not Load from json!!" << endl;
	c->die();
      }

      cout << "Loaded" << endl;

      Module* mainMod = c->getModule("global.main");

      c->runPasses({"rungenerators"});

      NGraph g;
      buildOrderedGraph(mainMod, g);

      deque<vdisc> topoOrder = topologicalSort(g);

      SECTION("Compile and run") {
	int s = compileCode(topoOrder, g, mainMod, "./gencode/", "mainMod");
	REQUIRE(s == 0);
      }

    }

    deleteContext(c);

  }


}
