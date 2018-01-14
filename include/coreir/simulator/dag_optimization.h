#pragma once

#include "coreir/simulator/op_graph.h"

namespace CoreIR {

  typedef std::deque<vdisc> SubDAG;

  class SIMDGroup {
  public:
    int totalWidth;
    std::vector<SubDAG> nodes;
  };

  struct CircuitPaths {
    std::vector<SIMDGroup > preSequentialAlwaysDAGs;
    std::vector<SIMDGroup > preSequentialDAGs;
    std::vector<SIMDGroup > postSequentialDAGs;
    std::vector<SIMDGroup > postSequentialAlwaysDAGs;
    std::vector<SIMDGroup > pureCombDAGs;
  };

  std::vector<SIMDGroup> deleteDuplicates(const std::vector<SIMDGroup>& allUpdates);

  std::vector<SIMDGroup> pruneSequentialSinks(const std::vector<SIMDGroup> dags,
                                              const NGraph& g);

  std::vector<SIMDGroup> pruneOutputs(const std::vector<SIMDGroup> dags,
                                      const NGraph& g);

  CircuitPaths buildCircuitPaths(const std::deque<vdisc>& topoOrder,
                                 NGraph& g,
                                 Module& mod);

  SubDAG addInputs(const SubDAG& dag, const NGraph& g);
  SubDAG addConstants(const SubDAG& dag, const NGraph& g);
  
}
