#pragma once

#include "coreir/simulator/codegen.h"
#include "coreir/simulator/layout.h"
#include "coreir/simulator/multithreading.h"

namespace CoreIR {

  std::string
  printSimFunctionBody(const std::deque<vdisc>& topo_order,
                       NGraph& g,
                       Module& mod,
                       const int threadNo,
                       const LayoutPolicy& layoutPolicy);

  std::string printCode(const ModuleCode& mc);

  ModuleCode buildCode(const std::deque<vdisc>& topoOrder,
                       NGraph& g,
                       CoreIR::Module* mod,
                       const std::string& baseName);

  std::string printDecl(const ModuleCode& mc);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  sortedSimArgumentPairs(Module& mod);


  ThreadGraph buildThreadGraph(const NGraph& opG);

  std::string seMacroDef();
  std::string maskMacroDef();

  typedef std::deque<vdisc> SubDAG;

  class SIMDGroup {
  public:
    int totalWidth;
    std::vector<SubDAG> nodes;
  };

  struct CircuitPaths {
    std::vector<SIMDGroup > preSequentialAlwaysDAGs;
    std::vector<SIMDGroup > preSequentialDAGs;
    std::vector<SIMDGroup > postSequentialDAGs;
    std::vector<SIMDGroup > postSequentialAlwaysDAGs;
    std::vector<SIMDGroup > pureCombDAGs;
  };

  CircuitPaths buildCircuitPaths(const std::deque<vdisc>& topoOrder,
                                 NGraph& g,
                                 Module& mod);

  SubDAG addInputs(const SubDAG& dag, const NGraph& g);
}
