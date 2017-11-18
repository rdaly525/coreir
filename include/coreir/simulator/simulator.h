#pragma once

#include "coreir/simulator/multithreading.h"

namespace CoreIR {

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
