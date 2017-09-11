#pragma once

#include "coreir.h"
#include "../../src/simulator/op_graph.hpp"

namespace CoreIR {

  int generateHarnessAndRun(const std::deque<vdisc>& topoOrder,
			    NGraph& g,
			    Module* mod,
			    const std::string& outFileBase,
			    const std::string& harnessFile);
  
  std::string randomSimInputString(Module* mod);

  std::string randomSimInputHarness(Module* mod);

}
