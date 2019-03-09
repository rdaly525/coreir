#include "coreir.h"
#include "coreir/tools/cxxopts.h"
#include <fstream>
#include <memory>
#include "passlib.h"

#include "coreir/common/logging_lite.hpp"

#include "coreir/passes/analysis/smtlib2.h"
#include "coreir/passes/analysis/smv.h"
#include "coreir/passes/analysis/firrtl.h"
#include "coreir/passes/analysis/magma.h"
#include "coreir/passes/analysis/coreirjson.h"
#include "coreir/passes/analysis/verilog.h"

#include "coreir/definitions/coreVerilog.hpp"
#include "coreir/definitions/corebitVerilog.hpp"
#include "coreir/definitions/coreFirrtl.hpp"
#include "coreir/definitions/corebitFirrtl.hpp"

using namespace std;
using namespace CoreIR;


string getExt(string s) {
  auto split = splitString<vector<string>>(s,'.');
  ASSERT(split.size()>=2,"File needs extention: " + s);
  return split[split.size()-1];
}

int main(int argc, char *argv[]) {
  int argc_copy = argc;
  cxxopts::Options options("coreir", "a simple hardware compiler");
  options.add_options()
    ("h,help","help")
    ("v,verbose","Set verbose")
    ("i,input","input file: '<file1>.json,<file2.json,...'",cxxopts::value<std::string>())
    ("o,output","output file: <file>.<json|fir|v|py|dot>",cxxopts::value<std::string>())
    ("p,passes","Run passes in order: '<pass1> <pass1args>;<pass2> <pass2args>;...'",cxxopts::value<std::string>())
    ("e,load_passes","external passes: '<path1.so>,<path2.so>,<path3.so>,...'",cxxopts::value<std::string>())
    ("l,load_libs","external libs: '<libname0>,<path/libname1.so>,<libname2>,...'",cxxopts::value<std::string>())
    ("n,namespaces","namespaces to output: '<namespace1>,<namespace2>,<namespace3>,...'",cxxopts::value<std::string>()->default_value("global"))
    ("t,top","top: <namespace>.<modulename>",cxxopts::value<std::string>())
    ("a,all","run on all namespaces")
    ("z,inline","inlines verilog primitives")
    ("y,verilator_debug","mark signals with /*veriltor public*/")
    ("s,split","splits output files by name (expects '-o <path>/*.<ext>')")
    ;
  
  //Do the parsing of the arguments
  auto opts = options.parse(argc,argv);
  
  Context* c = newContext();
  
  if (opts.count("l")) {
    vector<string> libs = splitString<vector<string>>(opts["l"].as<string>(),',');
    for (auto lib : libs) {
      c->getLibraryManager()->loadLib(lib);
    }
  }
   
  PassLibrary loadedPasses(c);
  if (opts.count("e")) {
    vector<string> passes = splitString<vector<string>>(opts["e"].as<string>(),',');
    for (auto pass : passes) {
      loadedPasses.loadPass(pass);
    }
  }
  
  if (opts.count("h") || argc_copy==1) {
    cout << options.help() << endl << endl;
    c->getPassManager()->printPassChoices();
    cout << endl;
    return 0;
  }
  
  if (opts.count("v")) {
    c->getPassManager()->setVerbosity(opts["v"].as<bool>());
  }

  ASSERT(opts.count("i"),"No input specified");
  string ilist = opts["i"].as<string>();
  vector<string> infileNames = splitString<vector<string>>(ilist,',');

  for (auto infileName : infileNames) {
    string inExt = getExt(infileName);
    ASSERT(inExt=="json","Input needs to be json");
  }

  const bool split_files = opts.count("s") && opts["s"].as<bool>();

  //Load inputs
  Module* top;
  string topRef = "";
  for (auto infileName : infileNames) {
    if (!loadFromFile(c,infileName,&top)) {
      c->die();
    }
    if (top) topRef = top->getRefName();
    if (opts.count("t")) {
      topRef = opts["t"].as<string>();
      c->setTop(topRef);
    }
  }
  
  vector<string> namespaces;
  if (opts.count("a")) {
    for (auto ns : c->getNamespaces()) {
      if (ns.first !="coreir" && ns.first !="corebit") {
        namespaces.push_back(ns.first);
      }
    }
  }
  else {
    namespaces = splitString<vector<string>>(opts["n"].as<string>(),',');
  }

  //Load and run passes
  bool modified = false;
  if (opts.count("p")) {
    string plist = opts["p"].as<string>();
    vector<string> porder = splitString<vector<string>>(plist,';');
    modified = c->runPasses(porder,namespaces);
  }

  std::ostream* sout = &std::cout;
  std::string outExt = "json";
  std::string output_dir = "";
  auto parse_outputs = [&] {
    std::string outfile = "";
    if (opts.count("o")) {
      outfile = opts["o"].as<string>();
      outExt = getExt(outfile);
      ASSERT(outExt == "json"
             || outExt == "txt"
             || outExt == "fir"
             || outExt == "py"
             || outExt == "smt2"
             || outExt == "smv"
             || outExt == "v", "Cannot support out extention: " + outExt);
      if (!split_files) {
        std::unique_ptr<std::ofstream> fout(new std::ofstream(outfile));
        ASSERT(fout->is_open(),"Cannot open file: " + outfile);
        sout = fout.release();
      }
    }
    if (split_files) {
      ASSERT(outExt == "v",
             "Split files option is only supported in verilog mode currently: "
             "ext = " + outExt);
      ASSERT(outfile != "", "Must specify outfile with '-o' to split files");
      const auto len = outfile.size();
      const auto ext_len = outExt.size();
      ASSERT(outfile.substr(len - (ext_len + 2), 2) == "*.",
             "Expected -o to be given as '<path>/*.<ext>'");
      output_dir = outfile.substr(0, len - (ext_len + 2));
      // TODO(rsetaluri): Check that output_dir exists and is a directory.
    }
  };
  parse_outputs();

  //Output to correct format
  if (outExt=="json") {
    c->runPasses({"coreirjson"},namespaces);
    auto jpass = static_cast<Passes::CoreIRJson*>(c->getPassManager()->getAnalysisPass("coreirjson"));
    string topref = "";
    if (c->hasTop()) {
      topref = c->getTop()->getRefName();
    }
    jpass->writeToStream(*sout,topref);
  }
  else if (outExt=="fir") {
    CoreIRLoadFirrtl_coreir(c);
    CoreIRLoadFirrtl_corebit(c);
    c->runPasses({"rungenerators","cullgraph","wireclocks-coreir","firrtl"},namespaces);
    //Get the analysis pass
    auto fpass = static_cast<Passes::Firrtl*>(c->getPassManager()->getAnalysisPass("firrtl"));
    
    //Create file here.
    fpass->writeToStream(*sout);
  }
  else if (outExt=="v") {
    // TODO: Have option to output this or not
    CoreIRLoadVerilog_coreir(c);
    CoreIRLoadVerilog_corebit(c);

    LOG(INFO) << "Running Runningvpasses";
    string vstr = "verilog";
    if (opts.count("z")) {
      vstr += " -i";
    }
    if (opts.count("y")) {
      vstr += " -y";
    }
    modified |= c->runPasses({"rungenerators","removebulkconnections","flattentypes",vstr},namespaces);
    LOG(INFO) << "Running vpasses";

    auto vpass = static_cast<Passes::Verilog*>(c->getPassManager()->getAnalysisPass("verilog"));

    if (split_files) {
      vpass->writeToFiles(output_dir);
    } else {
      vpass->writeToStream(*sout);
    }
  }
  else if (outExt=="py") {
    modified |= c->runPasses({"rungenerators","cullgraph","wireclocks-coreir","magma"});
    auto mpass = static_cast<Passes::Magma*>(c->getPassManager()->getAnalysisPass("magma"));
    mpass->writeToStream(*sout);
  }
  else if (outExt=="txt") {
    assert(top);
    if (!saveToDot(top,*sout)) {
      c->die();
    }
  }
  else if (outExt=="smt2") {
    modified |= c->runPasses({"removebulkconnections","flattentypes","smtlib2"});
    auto vpass = static_cast<Passes::SmtLib2*>(c->getPassManager()->getAnalysisPass("smtlib2"));
    
    vpass->writeToStream(*sout);
  }
  else if (outExt=="smv") {
    modified |= c->runPasses({"removebulkconnections","flattentypes","smv"});
    auto vpass = static_cast<Passes::SMV*>(c->getPassManager()->getAnalysisPass("smv"));
    
    vpass->writeToStream(*sout);
  }
  else {
    LOG(INFO) << "NYI";
  }
  LOG(INFO) << "Modified?: " << (modified ? "Yes" : "No");

  return 0;
}
