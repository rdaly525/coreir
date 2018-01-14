#pragma once

#include "coreir/simulator/codegen.h"
#include "coreir/simulator/layout.h"
#include "coreir/simulator/multithreading.h"
#include "coreir/simulator/subcircuit.h"
#include "coreir/simulator/wiring_utils.h"

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

}
