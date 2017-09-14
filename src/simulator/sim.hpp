#pragma once

#include "op_graph.hpp"

namespace CoreIR {

  //void buildOrderedGraph(CoreIR::Module* mod, NGraph& g);

  std::string printCode(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			CoreIR::Module* mod);

  string printDecl(CoreIR::Module* mod);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simArguments(Module& mod);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simInputs(Module& mod);
  
}
