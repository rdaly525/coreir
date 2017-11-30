#pragma once

#include "coreir/simulator/op_graph.h"

namespace CoreIR {
  class ModuleCode {
  public:

    const NGraph& g;
    CoreIR::Module* mod;

    ModuleCode(const NGraph& g_, CoreIR::Module* mod_) : g(g_), mod(mod_) {}

    std::vector<std::pair<CoreIR::Type*, std::string> > structLayout;
  };

  std::string printEvalStruct(const ModuleCode& mc);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  threadSharedVariableDecls(const NGraph& g);
  
}
