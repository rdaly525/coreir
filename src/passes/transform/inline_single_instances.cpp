#include "coreir/passes/transform/inline_single_instances.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

bool Passes::InlineSingleInstances::runOnInstanceGraphNode(
  InstanceGraphNode& node) {
  auto m = node.getModule();
  if (!m->hasDef()) { return false; }
  auto metadata = m->getMetaData();
  // Set metadata["inline_single_instance"] to false to skip this module
  if (
    metadata.count("inline_single_instance") &&
    !metadata["inline_single_instance"].get<bool>()) {
    return false;
  }

  auto numInstances = m->getDef()->getInstances().size();
  bool hasSingleInstance = numInstances == 1;
  if (!hasSingleInstance) { return false; }
  bool changed = false;
  for (auto inst : node.getInstanceList()) { changed |= inlineInstance(inst); }
  return changed;
}
