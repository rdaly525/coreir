#pragma once

#include "op_graph.hpp"

namespace CoreIR {

  //void buildOrderedGraph(CoreIR::Module* mod, NGraph& g);

  std::string printCode(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			CoreIR::Module* mod);

  std::string printDecl(CoreIR::Module* mod);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simArguments(CoreIR::Module& mod);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simInputs(CoreIR::Module& mod);
  
}
