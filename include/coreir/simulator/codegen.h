#pragma once

#include "coreir/simulator/op_graph.h"

namespace CoreIR {
  class ModuleCode {
  public:
    std::deque<vdisc> topoOrder;
    NGraph& g;
    CoreIR::Module* mod;
  };

}
