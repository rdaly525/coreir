#include "coreir.h"
#include "coreir/tools/cxxopts.h"
#include <fstream>

#include "passlib.h"

#include <string>

#include "coreir/passes/analysis/firrtl.h"
#include "coreir/passes/analysis/coreirjson.h"
#include "coreir/passes/analysis/verilog.h"
#include "coreir/simulator/interpreter.h"
#include "coreir/libs/commonlib.h"

using namespace std;
using namespace CoreIR;

string getExt(string s) {
  auto split = splitString<vector<string>>(s,'.');
  ASSERT(split.size()>=2,"File needs extention: " + s);
  return split[split.size()-1];
}

typedef std::map<std::string,std::pair<void*,Pass*>> OpenPassHandles_t;
typedef std::map<std::string,std::pair<void*,Namespace*>> OpenLibHandles_t;

int main(int argc, char *argv[]) {
  int argc_copy = argc;
  cxxopts::Options options("coreir", "a simple hardware compiler");
  options.add_options()
    ("h,help","help")
    ("v,verbose","Set verbose")
    ("i,input","input file: <file>.json",cxxopts::value<std::string>())
    ("o,output","output file: <file>.<json|fir|v|dot>",cxxopts::value<std::string>())
    ("p,passes","Run passes in order: '<pass1>,<pass2>,<pass3>,...'",cxxopts::value<std::string>())
    ("e,load_passes","external passes: '<path1.so>,<path2.so>,<path3.so>,...'",cxxopts::value<std::string>())
    ("l,load_libs","external libs: '<path/libname0.so>,<path/libname1.so>,<path/libname2.so>,...'",cxxopts::value<std::string>())
    ("n,namespaces","namespaces to output: '<namespace1>,<namespace2>,<namespace3>,...'",cxxopts::value<std::string>()->default_value("global"))
    ("t,top","top: <namespace>.<modulename>",cxxopts::value<std::string>())
    ;
  
  //Do the parsing of the arguments
  options.parse(argc,argv);
  
  OpenPassHandles_t openPassHandles;
  OpenLibHandles_t openLibHandles;
  
  
  Context* c = newContext();

  CoreIRLoadLibrary_commonlib(c);
  
  if (options.count("l")) {
    vector<string> libs = splitString<vector<string>>(options["l"].as<string>(),',');
    for (auto lib : libs) {
      c->getLibraryManager()->loadLib(lib);
    }
  }
   
  PassLibrary loadedPasses(c);
  if (options.count("e")) {
    vector<string> passes = splitString<vector<string>>(options["e"].as<string>(),',');
    for (auto pass : passes) {
      loadedPasses.loadPass(pass);
    }
  }

  if (options.count("h") || argc_copy==1) {
    cout << options.help() << endl << endl;
    c->getPassManager()->printPassChoices();
    cout << endl;
    return 0;
  }
  
  if (options.count("v")) {
    c->getPassManager()->setVerbosity(options["v"].as<bool>());
  }

  ASSERT(options.count("i"),"No input specified");
  string infileName = options["i"].as<string>();
  string inExt = getExt(infileName);
  ASSERT(inExt=="json","Input needs to be json");
  
  //std::ostream* sout = &std::cout;
  std::ofstream fout;
  string outExt = "json";
  if (options.count("o")) {
    string outfileName = options["o"].as<string>();
    outExt = getExt(outfileName);
    ASSERT(outExt == "json" 
        || outExt == "txt"
        || outExt == "fir"
        || outExt == "v", "Cannot support out extention: " + outExt);
    fout.open(outfileName);
    ASSERT(fout.is_open(),"Cannot open file: " + outfileName);
    //sout = &fout;
  }
  
  //Load input
  Module* top;
  string topRef = "";
  if (!loadFromFile(c,infileName,&top)) {
    c->die();
  }
  if (top) topRef = top->getRefName();
  if (options.count("t")) {
    topRef = options["t"].as<string>();
    c->setTop(topRef);
  }

  c->runPasses({"rungenerators","flattentypes","flatten","wireclocks-coreir"});

  SimulatorState state(top);

  string lastCommand = "";

  while (true) {
    std::cout << "> ";
    getline(std::cin, lastCommand);

    vector<string> args =
      splitString<vector<string>>(lastCommand, ' ');

    if (args.size() == 0) {
      continue;
    }

    string cmd = args[0];

    if (cmd == "quit") {
      std::cout << "Exiting..." << std::endl;
      break;
    } else if (cmd == "set") {
      if (args.size() == 3) {

        string valName = args[1];
        string bitString = args[2];

        int len = bitString.size();

        state.setValue(valName, BitVector(len, bitString));
      } else if (args.size() == 4) {
        string clkName  = args[1];
        string oldVal = args[2];
        string newVal = args[3];

        state.setClock(clkName, stoi(oldVal), stoi(newVal));
      } else {
        assert(false);
      }

    } else if (cmd == "print") {
      if (args.size() != 2) {
	cout << cmd << " requires " << 2 << " argument(s)" << endl;
	continue;
      }

      string ins = args[1];

      if (ins == "inputs") {
	auto& gr = state.getCircuitGraph();
	for (auto vd : gr.getVerts()) {

          if (isGraphInput(gr.getNode(vd))) {
	    cout << gr.getNode(vd).getWire()->toString() << " : " << gr.getNode(vd).getWire()->getType()->toString() << endl;
	  }

	}
	continue;
      }

      if (ins == "outputs") {
	auto& gr = state.getCircuitGraph();
	for (auto vd : gr.getVerts()) {

          if (isGraphOutput(gr.getNode(vd))) {
	    cout << gr.getNode(vd).getWire()->toString() << " : " << gr.getNode(vd).getWire()->getType()->toString() << endl;
	  }

	}
	continue;
      }

      if (!state.exists(ins)) {
	cout << ins << " does not exist "<< endl;
	continue;
      }

      if (!state.isSet(ins)) {
	cout << ins << " is not set "<< endl;
	continue;
      }

      //cout << "Getting bit vector" << endl;
      //BitVector bv = state.getBitVec(ins);
      SimValue* val = state.getValue(ins);

      if (val->getType() == SIM_VALUE_BV) {

        cout << static_cast<SimBitVector*>(val)->getBits() << endl;
      } else {
        assert(val->getType() == SIM_VALUE_CLK);

        ClockValue* clk = toClock(val);

        cout << "Last value    = " << (int)(clk->lastValue()) << endl;
        cout << "Current value = " << (int)(clk->value()) << endl;
      }
      
    } else if (cmd == "exec") {
      assert(args.size() == 1);

      state.runHalfCycle();
      state.runHalfCycle();

    } else if (cmd == "cycle-count") {
      if (args.size() != 1) {
        cout << "Error: Cycle count takes no arguments!" << endl;
        
      } else {

        cout << toClock(state.getValue(state.getMainClock()))->getCycleCount() << endl;
      }

    } else if (cmd == "watch") {
      if (args.size() != 3) {
        cout << "Error: watchpoint setting requires a name and value" << endl;
      } else {
        string name = args[1];
        string value = args[2];

        BitVector vec(value.size(), value);
        state.setWatchPoint(name, vec);
      } 
    } else if (cmd == "run") {
      if (args.size() != 1) {
        cout << "run takes no arguments!" << endl;
      } else {
        state.run();
      }
    } else if (cmd == "rewind") {
      if (args.size() != 2) {
        cout << "Error: rewind requires the number of cycles to rewind" << endl;
      } else {
        int cyclesToRewind = stoi(args[1]);
        state.rewind(2*cyclesToRewind);
      }
    } else if (cmd == "delete-watch") {
      if (args.size() != 2) {
        cout << "Error: delete-watch needs 1 argument" << endl;
      } else {
        state.deleteWatchPoint(args[1]);
      }
    } else {
      cout << "Unrecognized command: " << cmd << endl;
    }
  }

  //Shutdown
  return 0;
}
