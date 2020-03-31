#include "coreir.h"
#include "coreir/passes/transform/inline_single_instances.h"

using namespace std;
using namespace CoreIR;

string Passes::InlineSingleInstances::ID = "inline_single_instances";
bool Passes::InlineSingleInstances::runOnInstanceGraphNode(InstanceGraphNode& node) {
  auto m = node.getModule();
  if (!m->hasDef()) {
      return false;
  }
  auto numInstances = node.getModule()->getDef()->getInstances().size();
  bool hasSingleInstance = numInstances == 1;
  if (!hasSingleInstance) {
      return false;
  }
  bool changed = false;
  for (auto inst : node.getInstanceList()) {
      changed |= inlineInstance(inst);
  }
  return changed;
}
