#include "coreir.h"
#include "coreir-passes/transform/flatten.h"

using namespace CoreIR;

string Passes::Flatten::ID = "flatten";
bool Passes::Flatten::runOnInstanceGraphNode(InstanceGraphNode& node) {
  bool changed = false;
  for (auto inst : node.getInstanceList()) {
    changed |= inlineInstance(inst);
  }
  return changed;
}
