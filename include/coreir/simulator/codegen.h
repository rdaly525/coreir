#pragma once

#include "coreir/simulator/op_graph.h"

namespace CoreIR {

  std::vector<std::pair<CoreIR::Type*, std::string> >
  sortedSimArgumentPairs(Module& mod);

  class ModuleCode {
  public:

    const NGraph& g;
    CoreIR::Module* mod;

    std::vector<std::pair<CoreIR::Type*, std::string> > structLayout;

    std::string codeString;
    
    ModuleCode(const NGraph& g_, CoreIR::Module* mod_) : g(g_), mod(mod_) {
      structLayout = sortedSimArgumentPairs(*mod);
    }

  };

  std::string printEvalStruct(const ModuleCode& mc);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  threadSharedVariableDecls(const NGraph& g);
  
}
