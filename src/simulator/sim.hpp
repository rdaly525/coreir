#pragma once

#include "op_graph.hpp"

namespace CoreIR {

  std::string printCode(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			CoreIR::Module* mod,
			const std::string& baseName);

  std::string printDecl(CoreIR::Module* mod,
			const std::string& baseName);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simArguments(CoreIR::Module& mod);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simInputs(CoreIR::Module& mod);
  
}
