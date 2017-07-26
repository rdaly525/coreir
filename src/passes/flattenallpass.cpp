#include "coreir.h"
#include "coreir-passes/flattenallpass.hpp"

using namespace CoreIR;

bool FlattenAllPass::runOnInstanceGraphNode(InstanceGraphNode& node) {
  bool changed = false;
  for (auto inst : node.getInstanceList()) {
    changed |= inlineInstance(inst);
  }
  return changed;
}
