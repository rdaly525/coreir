#include "coreir.h"
#include "cxxopts.hpp"

#include "coreir-passes/firrtl.hpp"

using namespace CoreIR;

string getExt(string s) {
  auto split = splitString(s,'.');
  ASSERT(split.size()==2,"File needs extention: " + s);
  return split[1];
}

int main(int argc, char *argv[]) {
  
  cxxopts::Options options("coreir", "a simple hardware compiler");
  options.add_options()
    ("i,input","input: <file>.json",cxxopts::value<std::string>())
    ("o,output","output: <file>.<json|txt|firrtl|v>",cxxopts::value<std::string>())
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
      || outExt == "firrtl"
      || outExt == "v", "Cannot support out extention: " + outExt);

  cout << "in: " << infileName << endl;
  cout << "out: " << outfileName << endl;

  //Load input
  Context* c = newContext();
  Module* top;
  if (!loadFromFile(c,infileName,&top)) {
    c->die();
  }
  cout << "Loaded succesffully" << endl;
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


  PassManager* pm = new PassManager(c->getGlobal());
  
  if (outExt=="firrtl") {
    Firrtl* fpass = new Firrtl();
    pm->addPass(fpass,5);
    pm->run();
    fpass->writeToFile(outfileName);
  }
  //Get Namespace
  //Namespace* ns = top->getNamespace();
  ////Write out to a file
  //if (outExt == "json") {
  //  if (!saveToFile(ns,outfileName,top)) {
  //    c->die();
  //  }
  //}
  //else {
  //  cout << "NYI" << endl;
  //}
    
  return 0;
}
