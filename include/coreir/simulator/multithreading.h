#pragma once

#include "coreir/common/op_graph.h"

namespace CoreIR {

typedef NGraph ThreadGraph;

int numThreads(const ThreadGraph& g);

void balancedComponentsParallel(NGraph& gr);

std::vector<std::set<vdisc>> connectedComponentsIgnoringInputs(
  const NGraph& opG);

}  // namespace CoreIR
