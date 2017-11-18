#pragma once

#include "coreir/simulator/multithreading.h"

namespace CoreIR {

  class LayoutPolicy {
  public:
    virtual ~LayoutPolicy() {}

    virtual std::string lastClkVarName(InstanceValue& clk) const = 0;

    virtual std::string clkVarName(InstanceValue& clk) const = 0;

    virtual std::string outputVarName(CoreIR::Wireable& outSel) const = 0;

    virtual std::string outputVarName(const InstanceValue& val) const = 0;

  };

  std::string
  printSimFunctionBody(const std::deque<vdisc>& topo_order,
                       NGraph& g,
                       Module& mod,
                       const int threadNo,
                       const LayoutPolicy& layoutPolicy);
  
  std::string printCode(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			CoreIR::Module* mod,
			const std::string& baseName);

  std::string printDecl(CoreIR::Module* mod,
			const NGraph& g);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  sortedSimArgumentPairs(Module& mod);


  ThreadGraph buildThreadGraph(const NGraph& opG);

  std::string seMacroDef();
  std::string maskMacroDef();

}
