#pragma once

#include "coreir.h"

namespace CoreIR {

  int generateHarnessAndRun(const std::deque<vdisc>& topoOrder,
			    CoreIR::NGraph& g,
			    CoreIR::Module* mod,
			    const std::string& codeDir,
			    const std::string& outFileBase,
			    const std::string& harnessFile);
  
  std::string randomSimInputString(Module* mod);

  std::string randomSimInputHarness(Module* mod);

  int buildVerilator(CoreIR::Module* m,
		     CoreIR::Namespace* g);
  
}
