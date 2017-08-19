#include "coreir.h"
#include "cxxopts.hpp"
#include <dlfcn.h>
#include <fstream>

#include "coreir-passes/analysis/firrtl.h"
#include "coreir-passes/analysis/coreirjson.h"
#include "coreir-passes/analysis/verilog.h"

using namespace CoreIR;

string getExt(string s) {
  auto split = splitString<vector<string>>(s,'.');
  ASSERT(split.size()>=2,"File needs extention: " + s);
  return split[split.size()-1];
}

typedef std::map<std::string,std::pair<void*,Pass*>> PassHandle_t;

void shutdown(Context* c,PassHandle_t openPassHandles) {
  //Close all the open passes
  for (auto handle : openPassHandles) {
    //Load the registerpass
    delete_pass_t* deletePass = (delete_pass_t*) dlsym(handle.second.first,"deletePass");
    const char* dlsym_error = dlerror();
    if (dlsym_error) {
      cout << "ERROR: Cannot load symbol deletePass: " << dlsym_error << endl;
      continue;
    }
    deletePass(handle.second.second);
  }
  deleteContext(c);
}



int main(int argc, char *argv[]) {
  int argc_copy = argc;
  cxxopts::Options options("coreir", "a simple hardware compiler");
  options.add_options()
    ("h,help","help")
    ("v,verbose","Set verbose")
    ("i,input","input file: <file>.json",cxxopts::value<std::string>())
    ("o,output","output file: <file>.<json|fir|v|dot>",cxxopts::value<std::string>())
    ("p,passes","Run passes in order: '<pass0>,<pass1>,<pass2>,...'",cxxopts::value<std::string>())
    ("e,load_passes","external passes: '<path1.so>,<path2.so>,<path3.so>,...'",cxxopts::value<std::string>())
    ("l,load_libs","external libs: '<path1.so>,<path2.so>,<path3.so>,...'",cxxopts::value<std::string>())
    ;
  
  //Do the parsing of the arguments
  options.parse(argc,argv);
  
  Context* c = newContext();
  //Load external passes
  std::map<std::string,std::pair<void*,Pass*>> openPassHandles;
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
        shutdown(c,openPassHandles);
        return 1;
      }
      Pass* p = registerPass();
      ASSERT(p,"P is null");
      openPassHandles[lib] = {libHandle,p};
      c->addPass(p);
    }
  }
  
  //TODO Load libraries
  
  if (options.count("h") || argc_copy==1) {
    cout << options.help() << endl << endl;
    c->getPassManager()->printPassChoices();
    cout << endl;
    shutdown(c,openPassHandles);
    return 0;
  }
  
  if (options.count("v")) {
    c->getPassManager()->setVerbosity(options["v"].as<bool>());
  }

  ASSERT(options.count("i"),"No input specified")
  string infileName = options["i"].as<string>();
  string inExt = getExt(infileName);
  ASSERT(inExt=="json","Input needs to be json");
  
  std::ostream* sout = &std::cout;
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
    sout = &fout;
  }

  //Load input
  Module* top;
  if (!loadFromFile(c,infileName,&top)) {
    c->die();
  }
  string topRef = "";
  if (top) topRef = top->getRefName();
  //if (userTop) {
  //  auto tref = splitString<vector<string>>(topRef,".");
  //  ASSERT(c->hasNamespace(tref[0]),"Missing top : " + topRef);
  //  ASSERT(c->getNamespace(tref[0])->hasModule(tref[1]),"Missing top : " + topRef);
  //  Module* uTop = c->getNamespace(tref[0])->getModule(tref[1]);
  //  if (uTop != top) {
  //    cout << "WARNING: Overriding top="+uTop->getNamespace()->getName() + "." + uTop->getName() + " with top=" + topRef;
  //  }
  //  top = uTop;
  //}

  //Load and run passes
  bool modified = false;
  if (options.count("p")) {
    string plist = options["p"].as<string>();
    vector<string> porder = splitString<vector<string>>(plist,',');
    modified = c->runPasses(porder);
  }
  



  //Output to correct format
  if (outExt=="json") {
    c->runPasses({"coreirjson"});
    auto jpass = static_cast<Passes::CoreIRJson*>(c->getPassManager()->getAnalysisPass("coreirjson"));
    jpass->writeToStream(*sout,topRef);
  }
  else if (outExt=="fir") {
    c->runPasses({"firrtl"});
    //Get the analysis pass
    auto fpass = static_cast<Passes::Firrtl*>(c->getPassManager()->getAnalysisPass("firrtl"));
    
    //Create file here.
    fpass->writeToStream(*sout);
  }
  else if (outExt=="v") {
    c->runPasses({"removebulkconnections","flattentypes","verilog"});
    auto vpass = static_cast<Passes::Verilog*>(c->getPassManager()->getAnalysisPass("verilog"));
    
    vpass->writeToStream(*sout);
  }
  else {
    cout << "NYI" << endl;
  }
  cout << endl << "Modified?: " << (modified?"Yes":"No") << endl;

  //Close all the open libs
  for (auto handle : openPassHandles) {
    //Load the registerpass
    delete_pass_t* deletePass = (delete_pass_t*) dlsym(handle.second.first,"deletePass");
    const char* dlsym_error = dlerror();
    if (dlsym_error) {
      cout << "ERROR: Cannot load symbol deletePass: " << dlsym_error << endl;
      return 1;
    }
    deletePass(handle.second.second);
  }
  return 0;
}
