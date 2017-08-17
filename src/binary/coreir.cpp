#include "coreir.h"
#include "cxxopts.hpp"
#include <dlfcn.h>
#include <fstream>

#include "coreir-passes/analysis/firrtl.h"

using namespace CoreIR;

string getExt(string s) {
  auto split = splitString<vector<string>>(s,'.');
  ASSERT(split.size()==2,"File needs extention: " + s);
  return split[1];
}

int main(int argc, char *argv[]) {
  
  cxxopts::Options options("coreir", "a simple hardware compiler");
  options.add_options()
    ("i,input","input: <file>.json",cxxopts::value<std::string>())
    ("o,output","output: <file>.<json|txt|firrtl|v>",cxxopts::value<std::string>())
    ("p,passes","passes: '<pass0>,<pass1>,<pass2>,...'",cxxopts::value<std::string>())
    ("e,load_passes","load_passes: '<path1.so>,<path2.so>,<path3.so>,...'",cxxopts::value<std::string>())
    ("l,load_libs","load_libs: '<path1.so>,<path2.so>,<path3.so>,...'",cxxopts::value<std::string>())
    ;
  //Do the parsing of the arguments
  options.parse(argc,argv);
  
  ASSERT(options.count("i"),"No input specified")
  ASSERT(options.count("o"),"No output specified")
  string infileName;
  string outfileName;
  try {
    infileName = options["i"].as<string>();
    outfileName = options["o"].as<string>();
  //string topRef = a.get<string>("top");
  //bool userTop = topRef != "";
  } catch(cxxopts::option_requires_argument_exception& exc) {
    cout << exc.what() << endl;
    exit(1);
  }
  string inExt = getExt(infileName);
  ASSERT(inExt=="json","Input needs to be json");
  string outExt = getExt(outfileName);
  ASSERT(outExt == "json" 
      || outExt == "txt"
      || outExt == "fir"
      || outExt == "v", "Cannot support out extention: " + outExt);

  cout << "in: " << infileName << endl;
  cout << "out: " << outfileName << endl;

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
        return 1;
      }
      Pass* p = registerPass();
      ASSERT(p,"P is null");
      openPassHandles[lib] = {libHandle,p};
      c->addPass(p);
    }
  }
  
  //TODO Load libraries

  //Load input
  Module* top;
  if (!loadFromFile(c,infileName,&top)) {
    c->die();
  }
  //if (userTop) {
  //  auto tref = splitString(topRef,".");
  //  ASSERT(c->hasNamespace(tref[0]),"Missing top : " + topRef);
  //  ASSERT(c->getNamespace(tref[0])->hasModule(tref[1]),"Missing top : " + topRef);
  //  Module* uTop = c->getNamespace(tref[0])->getModule(tref[1]);
  //  if (uTop != top) {
  //    cout << "WARNING: Overriding top="+uTop->getNamespace()->getName() + "." + uTop->getName() + " with top=" + topRef;
  //  }
  //  top = uTop;
  //}

  //Load and run passes
  if (options.count("p")) {
    string plist = options["p"].as<string>();
    vector<string> porder = splitString<vector<string>>(plist,',');
    if (outExt=="fir") porder.push_back("firrtl");
    //if (outExt=="json") porder.push_back("createJson");
    bool modified = c->runPasses(porder);
    cout << "Modified?: " << modified << endl;
  }


  if (outExt=="fir") {
    //Get the analysis pass
    auto fpass = static_cast<Passes::Firrtl*>(c->getPassManager()->getAnalysisPass("firrtl"));
    
    //Create file here.
    std::ofstream file(outfileName);
    fpass->writeToStream(file);
  }
  else if (outExt=="json") {
    Namespace* ns = top->getNamespace();
    //Write out to a file
    if (!saveToFile(ns,outfileName,top)) {
      c->die();
    }
  }
  else {
    cout << "NYI" << endl;
  }
   

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
