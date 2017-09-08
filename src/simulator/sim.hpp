#pragma once

#include "op_graph.hpp"

namespace CoreIR {

  void buildOrderedGraph(CoreIR::Module* mod, NGraph& g);

  std::string printCode(const std::deque<vdisc>& topoOrder,
			NGraph& g,
			CoreIR::Module* mod);

  string printDecl(CoreIR::Module* mod);

}
