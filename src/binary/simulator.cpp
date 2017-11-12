#include "coreir.h"
#include "cxxopts.hpp"
#include <dlfcn.h>
#include <fstream>

#include "coreir/passes/analysis/firrtl.h"
#include "coreir/passes/analysis/coreirjson.h"
#include "coreir/passes/analysis/verilog.h"
#include "coreir/libs/commonlib.h"

#include "../simulator/output.hpp"
#include "../simulator/sim.hpp"
#include "../simulator/utils.hpp"

using namespace std;
using namespace CoreIR;

string getExt(string s) {
  auto split = splitString<vector<string>>(s,'.');
  ASSERT(split.size()>=2,"File needs extention: " + s);
  return split[split.size()-1];
}

typedef std::map<std::string,std::pair<void*,Pass*>> OpenPassHandles_t;
typedef std::map<std::string,std::pair<void*,Namespace*>> OpenLibHandles_t;

set<vdisc> connectedComponent(const vdisc v, NGraph& gr) {
  set<vdisc> cc;

  vector<vdisc> rem{v};

  while (rem.size() > 0) {
    vdisc nextNode = rem.back();
    rem.pop_back();

    cc.insert(nextNode);

    for (auto& ed : gr.inEdges(nextNode)) {
      vdisc other = gr.source(ed);
      vdisc thisN = gr.target(ed);

      assert(thisN == nextNode);

      if (cc.find(other) == end(cc)) {
        WireNode wd = gr.getNode(other);
        if (!isGraphInput(wd)) {
          rem.push_back(other);
        }
      }
    }

    for (auto& ed : gr.outEdges(nextNode)) {
      vdisc other = gr.target(ed);
      if (cc.find(other) == end(cc)) {
        WireNode wd = gr.getNode(other);
        if (!isGraphInput(wd)) {
          rem.push_back(other);
        }
        //rem.push_back(other);
      }
    }
    
  }

  return cc;
}

void balancedComponentsParallel(NGraph& gr) {
  set<vdisc> nodes;
  for (auto& vd : gr.getVerts()) {
    nodes.insert(vd);
  }

  int numComponents = 0;

  vector<set<vdisc> > ccs;
  for (auto& vd : gr.getVerts()) {

    WireNode wd = gr.getNode(vd);

    if (!isGraphInput(wd)) {
      if (nodes.find(vd) != end(nodes)) {
        set<vdisc> ccNodes =
          connectedComponent(vd, gr);

        //cout << "CC size = " << ccNodes.size() << endl;

        for (auto& ccNode : ccNodes) {
          nodes.erase(ccNode);

          WireNode w = gr.getNode(ccNode);
          w.setThreadNo(numComponents);
          gr.addVertLabel(ccNode, w);
        }
      

        ccs.push_back(ccNodes);
        numComponents++;
      }
    }
  }

  cout << "# of connected components = " << numComponents << endl;

  // Now balance the components
  //int nThreads = 2;
  int i = 0;
  for (auto& cc : ccs) {
    for (auto& vd : cc) {
      WireNode w = gr.getNode(vd);
      //w.setThreadNo((i % 2) + 1);
      w.setThreadNo((i % 2) + 1); 
      gr.addVertLabel(vd, w);
    }
    i++;
  }
}

int main(int argc, char *argv[]) {
  //int argc_copy = argc;
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
    ;
  
  //Do the parsing of the arguments
  options.parse(argc,argv);
  
  OpenPassHandles_t openPassHandles;
  OpenLibHandles_t openLibHandles;
  
  
  Context* c = newContext();

  CoreIRLoadLibrary_commonlib(c);
  
  ASSERT(options.count("i"),"No input specified")
  string infileName = options["i"].as<string>();
  string inExt = getExt(infileName);
  ASSERT(inExt=="json","Input needs to be json");
  
  //Load input
  Module* top;
  if (!loadFromFile(c,infileName,&top)) {
    c->die();
  }
  string topRef = "";
  if (top) topRef = top->getRefName();

  cout << "Starting passes" << endl;

  c->runPasses({"rungenerators","flattentypes","flatten", "wireclocks-coreir"});

  cout << "Done running passes" << endl;

  NGraph gr;
  buildOrderedGraph(top, gr);

  balancedComponentsParallel(gr);


  cout << "Starting topological sort" << endl;

  // Delete inputs from the order, since they do not need to
  // be printed out
  deque<vdisc> topoOrder = topologicalSort(gr);

  string codePath = "./";
  string codeFile = top->getName() + "_sim.cpp";
  string hFile = top->getName() + "_sim.h";

  writeBitVectorLib(codePath + "bit_vector.h");

  cout << "Writing out files" << endl;

  writeFiles(topoOrder, gr, top, codePath, codeFile, hFile);
  
  return 0;
}
