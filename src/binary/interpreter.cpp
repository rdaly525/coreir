#include "coreir.h"
#include "cxxopts.hpp"
#include <dlfcn.h>
#include <fstream>

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
bool shutdown(Context* c,OpenPassHandles_t openPassHandles, OpenLibHandles_t openLibHandles) {
  bool err = false;
  //Close all the open passes
  for (auto handle : openPassHandles) {
    //Load the registerpass
    delete_pass_t* deletePass = (delete_pass_t*) dlsym(handle.second.first,"deletePass");
    const char* dlsym_error = dlerror();
    if (dlsym_error) {
      err = true;
      cout << "ERROR: Cannot load symbol deletePass: " << dlsym_error << endl;
      continue;
    }
    deletePass(handle.second.second);
  }

  deleteContext(c);
  return !err;
}



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
  //Load external passes
  if (options.count("e")) {
    vector<string> libs = splitString<vector<string>>(options["e"].as<string>(),',');
    //Open all the libs
    for (auto lib : libs) {
      ASSERT(openPassHandles.count(lib)==0,"Cannot REopen " + lib);
      void* libHandle = dlopen(lib.c_str(),RTLD_LAZY);
      ASSERT(libHandle,"Cannot open file: " + lib);
      dlerror();
      //Load the registerpass
      register_pass_t* registerPass = (register_pass_t*) dlsym(libHandle,"registerPass");
      const char* dlsym_error = dlerror();
      if (dlsym_error) {
        cout << "ERROR: Cannot load symbol registerPass: " << dlsym_error << endl;
        shutdown(c,openPassHandles,openLibHandles);
        return 1;
      }
      Pass* p = registerPass();
      ASSERT(p,"P is null");
      openPassHandles[lib] = {libHandle,p};
      c->addPass(p);
    }
  }
  
  if (options.count("l")) {
    vector<string> files = splitString<vector<string>>(options["l"].as<string>(),',');
    for (auto file : files) {
      vector<string> f1parse = splitString<vector<string>>(file,'/');
      string libfile = f1parse[f1parse.size()-1];
      vector<string> f2parse = splitRef(libfile);
      ASSERT(f2parse[1]=="so" || f2parse[1]=="dylib","Bad file: " + file);
      string libname = f2parse[0].substr(10,f2parse[0].length()-10);

      ASSERT(openLibHandles.count(file)==0,"Cannot REopen " + file);
      void* libHandle = dlopen(file.c_str(),RTLD_LAZY);
      ASSERT(libHandle,"Cannot open file: " + file);
      dlerror();
      //Load the Libraries
      string funname = "ExternalLoadLibrary_"+libname;
      LoadLibrary_t* loadLib = (LoadLibrary_t*) dlsym(libHandle,funname.c_str());
      const char* dlsym_error = dlerror();
      if (dlsym_error) {
        cout << "ERROR: Cannot load symbol " << funname << ": " << dlsym_error << endl;
        shutdown(c,openPassHandles,openLibHandles);
        return 1;
      }
      Namespace* ns = loadLib(c);
      ASSERT(ns,"NS is null in file " + file);
      openLibHandles[file] = {libHandle,ns};
    }
  }
  
  if (options.count("h") || argc_copy==1) {
    cout << options.help() << endl << endl;
    c->getPassManager()->printPassChoices();
    cout << endl;
    if (!shutdown(c,openPassHandles,openLibHandles) ) return 1;
    return 0;
  }
  
  if (options.count("v")) {
    c->getPassManager()->setVerbosity(options["v"].as<bool>());
  }

  ASSERT(options.count("i"),"No input specified")
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

  CoreIRLoadLibrary_commonlib(c);

  c->runPasses({"rungenerators","flattentypes","flatten", "liftclockports-coreir", "wireclocks-coreir"});

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
      assert(args.size() == 3);

      string valName = args[1];
      string bitString = args[2];

      int len = bitString.size();

      state.setValue(valName, BitVector(len, bitString));

    } else if (cmd == "print") {
      if (args.size() != 2) {
	cout << cmd << " requires " << 2 << " argument(s)" << endl;
	continue;
      }

      string ins = args[1];

      if (ins == "inputs") {
	auto& gr = state.getCircuitGraph();
	for (auto vd : gr.getVerts()) {
	  if (getInputConnections(vd, gr).size() == 0) {
	    cout << gr.getNode(vd).getWire()->toString() << " : " << gr.getNode(vd).getWire()->getType()->toString() << endl;
	  }
	}
	continue;
      }

      if (ins == "outputs") {
	auto& gr = state.getCircuitGraph();
	for (auto vd : gr.getVerts()) {
	  if (getOutputConnections(vd, gr).size() == 0) {
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

      BitVector bv = state.getBitVec(ins);

      cout << bv << endl;
      
    } else if (cmd == "exec") {
      assert(args.size() == 1);

      state.execute();

    } else {
      cout << "Unrecognized command: " << cmd << endl;
    }
  }

  //Shutdown
  if (!shutdown(c,openPassHandles,openLibHandles) ) return 1;
  return 0;
}
