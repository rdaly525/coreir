#include "catch.hpp"

#include "coreir.h"
#include "coreir-passes/analysis/pass_sim.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/simulator/interpreter.h"
#include "coreir/libs/commonlib.h"

#include "fuzzing.hpp"

#include "../src/simulator/output.hpp"
#include "../src/simulator/sim.hpp"
#include "../src/simulator/utils.hpp"

#include <iostream>

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

namespace CoreIR {

  void addCounter(Context* c, Namespace* global) {

    //assert(false);
    Params counterParams = {{"width", c->Int()}};

    TypeGen* counterTypeGen =
      global->newTypeGen(
    			 "myCounterTypeGen",
    			 counterParams,
    			 [](Context* c, Values args) {
    			   uint width = args.at("width")->get<int>();
    			   return c->Record({
    			       {"en",c->BitIn()}, 
    				 {"out",c->Array(width,c->Bit())},
    				   {"clk",c->Named("coreir.clkIn")},
    				     });
    			 } //end lambda
    			 ); //end newTypeGen


    ASSERT(global->hasTypeGen("myCounterTypeGen"),"Can check for typegens in namespaces");

    Generator* counter = global->newGeneratorDecl("myCounter",counterTypeGen,counterParams);

    counter->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {

    	uint width = args.at("width")->get<int>();
      
	Values wArg({{"width", Const::make(c,width)}});
    	def->addInstance("ai","coreir.add",wArg);
    	def->addInstance("ci",
			 "coreir.const",
			 wArg,
			 {{"value", Const::make(c, BitVector(width, 1))}});

    	def->addInstance("ri","mantle.reg",{{"width", Const::make(c,width)}, {"has_en", Const::make(c,true)}});
    

    	def->connect("self.clk","ri.clk");
    	def->connect("self.en","ri.en");
    	def->connect("ci.out","ai.in0");
    	def->connect("ai.out","ri.in");
    	def->connect("ri.out","ai.in1");
    	def->connect("ri.out","self.out");
      }); //end lambda, end function
  
  }
  
  TEST_CASE("Interpret simulator graphs") {

    // New context
    Context* c = newContext();
  
    Namespace* g = c->getGlobal();

    SECTION("andr") {
      uint n = 11;

      Generator* andr = c->getGenerator("coreir.andr");
      Type* andrNType = c->Record({
	  {"in", c->Array(n, c->BitIn())},
	    {"out", c->Bit()}
	});

      Module* andrN = g->newModuleDecl("andrN", andrNType);
      ModuleDef* def = andrN->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* andr0 = def->addInstance("andr0", andr, {{"width", Const::make(c,n)}});
    
      def->connect(self->sel("in"), andr0->sel("in"));
      def->connect(andr0->sel("out"),self->sel("out"));

      andrN->setDef(def);

      c->runPasses({"rungenerators","flattentypes","flatten"});
      // RunGenerators rg;
      // rg.runOnNamespace(g);

      SimulatorState state(andrN);

      SECTION("Bitvector that is all ones") {
	state.setValue("self.in", BitVec(n, "11111111111"));

	state.execute();

	REQUIRE(state.getBitVec("self.out") == BitVec(1, 1));
      }

      SECTION("Bitvector that is not all ones") {
	state.setValue("self.in", BitVec(n, "11011101111"));

	state.execute();

	REQUIRE(state.getBitVec("self.out") == BitVec(1, 0));
      }
      
    }

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
      Wireable* and_00 = def->addInstance("and00",and2,{{"width", Const::make(c,n)}});
      Wireable* and_01 = def->addInstance("and01",and2,{{"width", Const::make(c,n)}});
      Wireable* and_1 = def->addInstance("and1",and2,{{"width", Const::make(c,n)}});
    
      def->connect(self->sel("in0"), and_00->sel("in0"));
      def->connect(self->sel("in1"), and_00->sel("in1"));
      def->connect(self->sel("in2"), and_01->sel("in0"));
      def->connect(self->sel("in3"), and_01->sel("in1"));

      def->connect(and_00->sel("out"),and_1->sel("in0"));
      def->connect(and_01->sel("out"),and_1->sel("in1"));

      def->connect(and_1->sel("out"),self->sel("out"));
      and4_n->setDef(def);

      c->runPasses({"rungenerators","flattentypes","flatten"});      
      // RunGenerators rg;
      // rg.runOnNamespace(g);

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

      cout << "BV     = " << bv << endl;
      cout << "output = " << state.getBitVec(self->sel("out")) << endl;

      REQUIRE(state.getBitVec(self->sel("out")) == bv);
    }

    SECTION("Or 4") {
      cout << "23 bit or 4" << endl;

      uint n = 23;
  
      Generator* or2 = c->getGenerator("coreir.or");

      // Define Or4 Module
      Type* or4Type = c->Record({
	  {"in0",c->Array(n,c->BitIn())},
	    {"in1",c->Array(n,c->BitIn())},
	      {"in2",c->Array(n,c->BitIn())},
		{"in3",c->Array(n,c->BitIn())},
		  {"outval",c->Array(n,c->Bit())}
	});

      Module* or4_n = g->newModuleDecl("Or4",or4Type);
      ModuleDef* def = or4_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* or_00 = def->addInstance("or00",or2,{{"width", Const::make(c,n)}});
      Wireable* or_01 = def->addInstance("or01",or2,{{"width", Const::make(c,n)}});
      Wireable* or_1 = def->addInstance("or1",or2,{{"width", Const::make(c,n)}});
    
      def->connect(self->sel("in0"), or_00->sel("in0"));
      def->connect(self->sel("in1"), or_00->sel("in1"));
      def->connect(self->sel("in2"), or_01->sel("in0"));
      def->connect(self->sel("in3"), or_01->sel("in1"));

      def->connect(or_00->sel("out"), or_1->sel("in0"));
      def->connect(or_01->sel("out"), or_1->sel("in1"));

      def->connect(or_1->sel("out"), self->sel("outval"));
      or4_n->setDef(def);

      c->runPasses({"rungenerators","flattentypes"}); //,"flatten"});

      // RunGenerators rg;
      // rg.runOnNamespace(g);

      // How to initialize or track values in the interpreter?
      // I think the right way would be to set select values, but
      // that does not deal with registers or memory that need
      // intermediate values
      SimulatorState state(or4_n);

      state.setValue("self.in0", BitVec(n, 20));
      state.setValue(self->sel("in1"), BitVec(n, 0));
      state.setValue(self->sel("in2"), BitVec(n, 9));
      state.setValue(self->sel("in3"), BitVec(n, 31));

      state.execute();

      BitVec bv(n, 20 | 0 | 9 | 31);

      cout << "BV     = " << bv << endl;
      cout << "output = " << state.getBitVec(self->sel("outval")) << endl;

      REQUIRE(state.getBitVec(self->sel("outval")) == bv);
    }

    SECTION("Counter") {

      addCounter(c, g);

      uint pcWidth = 17;
      Type* counterTestType =
    	c->Record({
    	    {"en", c->BitIn()},
    	      {"clk", c->Named("coreir.clkIn")},
    		{"counterOut", c->Array(pcWidth, c->Bit())}});

      Module* counterTest = g->newModuleDecl("counterMod", counterTestType);
      ModuleDef* def = counterTest->newModuleDef();

      auto ct = def->addInstance("counter", "global.myCounter", {{"width", Const::make(c,pcWidth)}});

      def->connect("self.en", "counter.en");
      def->connect("self.clk", "counter.clk");
      def->connect("counter.out", "self.counterOut");

      counterTest->setDef(def);

      c->runPasses({"rungenerators", "flattentypes","flatten"});

      cout << "ct is generator ? " << ct->isGen() << endl;

      // bool inlinedCounter = inlineInstance(ct);

      // cout << "Inlined counter = " << inlinedCounter << endl;

      SimulatorState state(counterTest);

      NGraph& g = state.getCircuitGraph();

      cout << "COUNTER NODES" << endl;
      for (auto& vd : g.getVerts()) {
    	cout << g.getNode(vd).getWire()->toString() << endl;
      }
      cout << "DONE NODES." << endl;

      SECTION("Test register defaults") {
    	REQUIRE(state.getBitVec("counter$ri$reg0.out") == BitVec(pcWidth, 0));
      }

      SECTION("Test setting and getting registers") {
        state.setRegister("counter$ri$reg0", BitVec(pcWidth, 231));

        auto states = state.getCircStates();

        cout << "# of states = " << states.size() << endl;

        cout << "Register values" << endl;
        for (auto& regVal : states.back().registers) {
          cout << regVal.first << " = " << regVal.second << endl;
        }
        cout << "reg done." << endl;


        REQUIRE(state.getRegister("counter$ri$reg0") == BitVec(pcWidth, 231));
      }

      SECTION("Count from zero, enable set") {

        state.setRegister("counter$ri$reg0", BitVec(pcWidth, 0));
    	state.setValue("self.en", BitVec(1, 1));
    	state.setClock("self.clk", 0, 1);

    	state.execute();

        SECTION("After first cycle the output is the initial value") {
          REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 0));
        }

    	state.execute();

        SECTION("Next cycle the value is 1") {
          REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 1));
        }

    	state.execute();

        SECTION("At cycle 3 the value is 2") {
          REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 2));
        }

      }

      SECTION("Counting with clock changes, enable set") {

    	//state.setValue("counter$ri$reg0.out", BitVec(pcWidth, 400));
        state.setRegister("counter$ri$reg0", BitVec(pcWidth, 400));
    	state.setValue("self.en", BitVec(1, 1));
    	state.setClock("self.clk", 0, 1);
  
    	state.execute();

    	cout << "Output = " << state.getBitVec("self.counterOut") << endl;

    	SECTION("Value is 400 after first tick at 400") {
    	  REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 400));
    	}

    	state.setClock("self.clk", 1, 0);

    	state.execute();

    	ClockValue* clkVal = toClock(state.getValue("self.clk"));

    	cout << "last clock = " << (int) clkVal->lastValue() << endl;
    	cout << "curr clock = " << (int) clkVal->value() << endl;

    	cout << "Output = " << state.getBitVec("self.counterOut") << endl;

    	SECTION("Value is 401 after second tick") {
    	  REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 401));
    	}

    	state.setClock("self.clk", 0, 1);

    	state.execute();

    	SECTION("Value is still 401") {
    	  REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 401));
    	}

    	state.setClock("self.clk", 1, 0);

    	state.execute();

    	SECTION("Value is now 402") {
    	  REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 402));
    	}
	
      }

      SECTION("Enable on") {

        state.setRegister("counter$ri$reg0", BitVec(pcWidth, 400));
    	state.setValue("self.en", BitVec(1, 1));
    	state.setClock("self.clk", 1, 0);
  
    	state.execute();

    	cout << "Output = " << state.getBitVec("self.counterOut") << endl;

    	REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 400));
      }

      SECTION("Setting watchpoint") {

        state.setRegister("counter$ri$reg0", BitVec(pcWidth, 0));
        state.setClock("self.clk", 1, 0);
        state.setValue("self.en", BitVec(1, 1));

        state.setWatchPoint("self.counterOut", BitVec(pcWidth, 10));
        //state.setMainClock("self.clk");

        state.run();

        SECTION("Stop at watchpoint") {
          REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 10));
        }

        // Should rewind rewind 1 clock cycle or one half clock?
        SECTION("Rewinding state by 1 clock cycle") {

          cout << "state index before rewind = " << state.getStateIndex() << endl;
          state.rewind(2);
          cout << "state index after rewind  = " << state.getStateIndex() << endl;

          REQUIRE(state.getBitVec("self.counterOut") == BitVec(pcWidth, 9));
        }

        SECTION("Rewinding the changes clock cycle count") {

          ClockValue* clk = toClock(state.getValue("self.clk"));

          int oldCount = clk->getHalfCycleCount();

          state.rewind(3);

          ClockValue* clockAfterRewind = toClock(state.getValue("self.clk"));
          int newCount = clockAfterRewind->getHalfCycleCount();

          REQUIRE(newCount == (oldCount - 3));

          state.runHalfCycle();

          ClockValue* clockLater = toClock(state.getValue("self.clk"));

          int countLater = clockLater->getHalfCycleCount();

          REQUIRE(countLater == (newCount + 1));
        }

        SECTION("Setting a value after rewinding reverts all earlier states") {

          int numStates = state.getCircStates().size();

          state.rewind(2);

          REQUIRE(!state.atLastState());

          state.setValue("self.en", BitVec(1, 0));

          REQUIRE(state.atLastState());

          REQUIRE(state.getCircStates().size() == (numStates - 2));
        }

        SECTION("Rewinding and then running to an already simulated point fast forwards") {
          state.rewind(4);

          int numStates = state.getCircStates().size();

          state.runHalfCycle();

          REQUIRE(state.getCircStates().size() == numStates);
	  
        }

        SECTION("Rewinding to before the start of the simulation is an error") {

          bool rewind = state.rewind(22);

          REQUIRE(!rewind);
        }
      }

    }

    SECTION("Test bit vector addition") {
      cout << "23 bit or 4" << endl;

      uint n = 76;
  
      Generator* add2 = c->getGenerator("coreir.add");

      // Define Add2 Module
      Type* add2Type = c->Record({
	  {"in0",c->Array(n,c->BitIn())},
	    {"in1",c->Array(n,c->BitIn())},
	      {"outval",c->Array(n,c->Bit())}
	});

      Module* add2_n = g->newModuleDecl("Add2",add2Type);
      ModuleDef* def = add2_n->newModuleDef();
      Wireable* self = def->sel("self");
      Wireable* or_00 = def->addInstance("or00",add2,{{"width", Const::make(c,n)}});

      def->connect(self->sel("in0"), or_00->sel("in0"));
      def->connect(self->sel("in1"), or_00->sel("in1"));
      def->connect(or_00->sel("out"), self->sel("outval"));

      add2_n->setDef(def);

      // RunGenerators rg;
      // rg.runOnNamespace(g);

      c->runPasses({"rungenerators","flattentypes","flatten"});      

      // How to initialize or track values in the interpreter?
      // I think the right way would be to set select values, but
      // that does not deal with registers or memory that need
      // intermediate values
      SimulatorState state(add2_n);
      //state.setValue(self->sel("in0"), BitVec(n, 20));
      state.setValue("self.in0", BitVec(n, 20));
      state.setValue("self.in1", BitVec(n, 1234));

      state.execute();

      BitVec bv(n, 20 + 1234);

      cout << "BV     = " << bv << endl;
      cout << "output = " << state.getBitVec(self->sel("outval")) << endl;

      REQUIRE(state.getBitVec(self->sel("outval")) == bv);
      
    }

    SECTION("Multiplexer") {
      uint width = 30;

      Type* muxType =
	c->Record({
	    {"in0", c->Array(width, c->BitIn())},
	      {"in1", c->Array(width, c->BitIn())},
		{"sel", c->BitIn()},
		  {"out", c->Array(width, c->Bit())}
	  });

      Module* muxTest = g->newModuleDecl("muxTest", muxType);
      ModuleDef* def = muxTest->newModuleDef();

      Wireable* mux = def->addInstance("m0", "coreir.mux", {{"width", Const::make(c,width)}});

      def->connect("self.in0", "m0.in0");
      def->connect("self.in1", "m0.in1");
      def->connect("self.sel", "m0.sel");
      def->connect("m0.out", "self.out");

      muxTest->setDef(def);

      SECTION("Select input 1") {
	SimulatorState state(muxTest);
	state.setValue("self.in0", BitVec(width, 1234123));
	state.setValue("self.in1", BitVec(width, 987));
	state.setValue("self.sel", BitVec(1, 1));

	state.execute();

	REQUIRE(state.getBitVec("self.out") == BitVec(width, 987));
      }

      SECTION("Select input 0") {
	SimulatorState state(muxTest);
	state.setValue("self.in0", BitVec(width, 1234123));
	state.setValue("self.in1", BitVec(width, 987));
	state.setValue("self.sel", BitVec(1, 0));

	state.execute();

	REQUIRE(state.getBitVec("self.out") == BitVec(width, 1234123));
      }
      
    }

    SECTION("Increment circuit") {
      uint width = 3;

      Type* incTestType =
	c->Record({{"incIn", c->Array(width, c->BitIn())},
	      {"incOut", c->Array(width, c->Bit())}});

      Module* incTest = g->newModuleDecl("incMod", incTestType);
      ModuleDef* def = incTest->newModuleDef();

      //assert(false);
      // Value wArg({{"width", Const::make(c,width)}});
      Values wArg({{"width", Const::make(c,width)}});
      def->addInstance("ai","coreir.add",wArg);
      def->addInstance("ci","coreir.const",wArg,{{"value",
	      Const::make(c, BitVector(width, 1))}});
    
      def->connect("ci.out","ai.in0");
      def->connect("self.incIn","ai.in1");
      def->connect("ai.out","self.incOut");

      incTest->setDef(def);

      SimulatorState state(incTest);
      state.setValue("self.incIn", BitVec(width, 0));

      state.execute();

      REQUIRE(state.getBitVec("self.incOut") == BitVec(width, 1));
      
      
    }

    SECTION("LineBufferMem") {
      uint index = 2;
      uint width = index;
      uint depth = pow(2, index);

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

      def->addInstance("m0",
        	       "commonlib.LinebufferMem",
        	       {{"width", Const::make(c, width)},
        		   {"depth", Const::make(c, depth)}});

      def->connect("self.clk", "m0.clk");
      def->connect("self.wen", "m0.wen");
      def->connect("self.wdata", "m0.wdata");
      def->connect("m0.rdata", "self.rdata");
      def->connect("m0.valid", "self.valid");

      lbMem->setDef(def);

      c->runPasses({"rungenerators","flattentypes", "flatten"});
      //, "verifyconnectivity"}); //, {"commonlib", "mantle", "global"}); //,"flatten"});

      if (!saveToFile(g, "linebuffermem.json", lbMem)) {
        cout << "Could not save to json!!" << endl;
        c->die();
      }
      
      SimulatorState state(lbMem);

      state.setValue("self.wdata", BitVector(width, "11"));
      state.setValue("self.wen", BitVector(1, "1"));
      //state.setMainClock("self.clk");
      state.setClock("self.clk", 0, 1);

      // SECTION("Before execution valid is 0") {
      //   REQUIRE(state.getBitVec("m0.valid") == BitVec(1, 0));
      // }

      state.execute();

      SECTION("Before peek value was written valid is still 0") {
        REQUIRE(state.getBitVec("self.valid") == BitVec(1, 0));
      }

      for (int i = 0; i < 10; i++) {
        state.execute();
      }

      SECTION("rdata is 11 in steady state") {
        REQUIRE(state.getBitVec("self.rdata") == BitVec(width, "11"));
      }

      // SECTION("valid is set to one in steady state") {
      //   REQUIRE(state.getBitVec("self.valid") == BitVec(1, 1));
      // }
    }

    SECTION("Memory") {
      uint width = 20;
      uint depth = 4;
      uint index = 2;

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
      		       {{"width", Const::make(c,width)},{"depth", Const::make(c,depth)}});
		       //      		       {{"init", Const::make(c,BitVector(80))}});

      def->connect("self.clk", "m0.clk");
      def->connect("self.write_en", "m0.wen");
      def->connect("self.write_data", "m0.wdata");
      def->connect("self.write_addr", "m0.waddr");
      def->connect("self.read_data", "m0.rdata");
      def->connect("self.read_addr", "m0.raddr");

      memory->setDef(def);

      c->runPasses({"rungenerators","flattentypes","flatten"});      

      SimulatorState state(memory);

      SECTION("Memory default is zero") {
	REQUIRE(state.getMemory("m0", BitVec(index, 0)) == BitVec(width, 0));
      }

      SECTION("rdata default is zero") {
	REQUIRE(state.getBitVec("m0.rdata") == BitVec(width, 0));
      }
      
      state.setMemory("m0", BitVec(index, 0), BitVec(width, 0));
      state.setMemory("m0", BitVec(index, 1), BitVec(width, 1));
      state.setMemory("m0", BitVec(index, 2), BitVec(width, 2));
      state.setMemory("m0", BitVec(index, 3), BitVec(width, 3));

      SECTION("Setting memory manually") {
	REQUIRE(state.getMemory("m0", BitVec(index, 2)) == BitVec(width, 2));
      }

      SECTION("Re-setting memory manually") {
	state.setMemory("m0", BitVec(index, 3), BitVec(width, 23));

	REQUIRE(state.getMemory("m0", BitVec(index, 3)) == BitVec(width, 23));
      }

      SECTION("Write to address zero") {
      	state.setClock("self.clk", 0, 1);
      	state.setValue("self.write_en", BitVec(1, 1));
      	state.setValue("self.write_addr", BitVec(index, 0));
      	state.setValue("self.write_data", BitVec(width, 23));
      	state.setValue("self.read_addr", BitVec(index, 0));

      	state.execute();

	SECTION("read_data is zero initially") {
	  REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 0));
	}

      	state.execute();

	SECTION("One cycle after setting write_data the result has been updated") {
	  REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 23));
	}

      	state.execute();

      	cout << "read data later = " << state.getBitVec("self.read_data") << endl;

	SECTION("Re-updating does not change the value") {
	  REQUIRE(state.getBitVec("self.read_data") == BitVec(width, 23));
	}
	
      }
      
    }

    SECTION("Slice") {
      uint inLen = 7;
      uint lo = 2;
      uint hi = 5;
      uint outLen = hi - lo;

      Type* sliceType = c->Record({
	  {"in", c->Array(inLen, c->BitIn())},
	    {"out", c->Array(outLen, c->Bit())}
	});

      Module* sliceM = c->getGlobal()->newModuleDecl("sliceM", sliceType);
      ModuleDef* def = sliceM->newModuleDef();

      def->addInstance("sl",
		       "coreir.slice",
		       {{"width", Const::make(c,inLen)},
			   {"lo", Const::make(c,lo)},
			     {"hi", Const::make(c,hi)}});

      def->connect("self.in", "sl.in");
      def->connect("sl.out", "self.out");

      sliceM->setDef(def);

      SimulatorState state(sliceM);
      state.setValue("self.in", BitVec(inLen, "1011010"));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(outLen, "110"));
    }

    SECTION("Concat") {
      uint inLen0 = 3;
      uint inLen1 = 5;
      uint outLen = inLen0 + inLen1;

      Type* concatType = c->Record({
	  {"in0", c->BitIn()->Arr(inLen0)},
	    {"in1", c->BitIn()->Arr(inLen1)},
	      {"out", c->Bit()->Arr(outLen)}
	});

      Module* concatM = c->getGlobal()->newModuleDecl("concatM", concatType);
      ModuleDef* def = concatM->newModuleDef();

      def->addInstance("cm",
		       "coreir.concat",
		       {{"width0", Const::make(c,inLen0)},
			   {"width1", Const::make(c,inLen1)}});

      def->connect("self.in0", "cm.in0");
      def->connect("self.in1", "cm.in1");
      def->connect("cm.out", "self.out");

      concatM->setDef(def);

      SimulatorState state(concatM);
      state.setValue("self.in0", BitVec(3, "111"));
      state.setValue("self.in1", BitVec(5, "00000"));

      state.execute();

      REQUIRE(state.getBitVec("self.out") == BitVec(8, "00000111"));
    }

    SECTION("Lookup table") {
      uint n = 4;

      CoreIRLoadLibrary_commonlib(c);

      Generator* lutN = c->getGenerator("commonlib.lutN");
      Type* lutNType = c->Record({
	  {"in", c->Array(n, c->BitIn())},
	    {"out", c->Bit()}
	});

      Module* lut4 = g->newModuleDecl("lut4", lutNType);
      ModuleDef* def = lut4->newModuleDef();

      Wireable* self = def->sel("self");
      Wireable* lut0 =
	def->addInstance("lut0",
			 lutN,
			 {{"N", Const::make(c,n)}},
			 {{"init",
			       Const::make(c,
					   BitVector(1 << n, "1010010111010010"))}});

      def->connect(self->sel("in"), lut0->sel("in"));
      def->connect(lut0->sel("out"),self->sel("out"));

      lut4->setDef(def);

      c->runPasses({"rungenerators","flattentypes","flatten"});

      SimulatorState state(lut4);

      SECTION("lut(6) == 1") {
	state.setValue("self.in", BitVector(n, "0110"));

	state.execute();

	REQUIRE(state.getBitVec("self.out") == BitVec(1, 1));
      }

      SECTION("lut(0) == 0") {
	state.setValue("self.in", BitVector(n, "0000"));

	state.execute();

	REQUIRE(state.getBitVec("self.out") == BitVec(1, 0));
      }

    }

    SECTION("D flip flop") {
      Namespace* common = CoreIRLoadLibrary_commonlib(c);

      
      Module* dff = c->getModule("corebit.dff");
      Type* dffType = c->Record({
          {"IN", c->BitIn()},
            {"CLK", c->Named("coreir.clkIn")},
                {"OUT", c->Bit()}
        });

      Module* dffTest = g->newModuleDecl("dffTest", dffType);
      ModuleDef* def = dffTest->newModuleDef();

      Wireable* dff0 =
        def->addInstance("dff0",
        		 dff,
        		 {{"init", Const::make(c, true)}});

      Wireable* self = def->sel("self");
      def->connect("self.IN", "dff0.in");
      def->connect("self.CLK", "dff0.clk");
      def->connect("dff0.out", "self.OUT");

      dffTest->setDef(def);

      c->runPasses({"rungenerators","flattentypes","flatten"});

      // cout << "loading" << endl;
      // if (!loadFromFile(c,"./topo_sort_error.json")) {
      //   cout << "Could not Load from json!!" << endl;
      //   c->die();
      // }

      // Module* m = g->getModule("simple");

      SimulatorState state(dffTest);
      state.setClock("self.CLK", 0, 1);
      state.setValue("self.IN", BitVec(1, 0));

      state.execute();

      REQUIRE(state.getBitVec("self.OUT") == BitVec(1, 1));

      state.execute();

      REQUIRE(state.getBitVec("self.OUT") == BitVec(1, 0));

    }

    SECTION("Selecting bits from a bit vector") {
      Namespace* common = CoreIRLoadLibrary_commonlib(c);

      cout << "loading" << endl;
      if (!loadFromFile(c,"./sim_ready_sorter.json")) {
    	cout << "Could not Load from json!!" << endl;
    	c->die();
      }

      Module* m = g->getModule("Sorter8");

      assert(m != nullptr);

      SimulatorState state(m);
      state.setValue("self.I", BitVector(8, "10010011"));

      cout << "# of nodes in circuit = " << state.getCircuitGraph().getVerts().size() << endl;

      BitVector one(16, "1");
      BitVector nextIn(16, "0");

      std::clock_t start, end;

      start = std::clock();

      state.execute();

      end = std::clock();

      std::cout << "Done. Time to simulate = "
    		<< (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    		<< std::endl;

      
      cout << "out = " << state.getBitVec("self.O") << endl;

      REQUIRE(state.getBitVec("self.O") == BitVector(8, "11110000"));
    }

    SECTION("Failing clock test") {

      cout << "loading" << endl;
      if (!loadFromFile(c,"./simple_register_example.json")) {
    	cout << "Could not Load from json!!" << endl;
    	c->die();
      }

      Module* regMod = g->getModule("simple_flattened");
      SimulatorState state(regMod);

      SECTION("2 unset inputs") {
        REQUIRE(state.unsetInputs().size() == 2);
      }

      state.execute();

      state.setClock("self.CLK", 0, 1);

      SECTION("1 unset inputs") {
        REQUIRE(state.unsetInputs().size() == 1);
      }
      
      state.setValue("self.I0", BitVec(2, "11"));

      SECTION("0 unset inputs") {
        REQUIRE(state.unsetInputs().size() == 0);
      }
      
      state.execute();
      state.execute();

      SimValue* val = state.getValue("self.CLK");
      assert(val->getType() == SIM_VALUE_CLK);

      ClockValue* clkVal = static_cast<ClockValue*>(val);

      REQUIRE(state.getBitVec("self.O") == BitVec(2, "11"));
      REQUIRE(clkVal->value() == 1);
      REQUIRE(clkVal->lastValue() == 0);
      
      
    }

    deleteContext(c);
  }

  TEST_CASE("Name generation") {
    vector<string> strs{"counter", "ri", "dummy.out"};

    REQUIRE(concatInlined(strs) == "counter$ri$dummy.out");
  }


}
