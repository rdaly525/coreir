#pragma once

#include "op_graph.hpp"

namespace CoreIR {

  typedef NGraph ThreadGraph;

  int numThreads(const ThreadGraph& g);

  std::string printCode(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			CoreIR::Module* mod,
			const std::string& baseName);

  std::string printDecl(CoreIR::Module* mod,
			const std::string& baseName);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  sortedSimArgumentPairs(Module& mod);
  
}
