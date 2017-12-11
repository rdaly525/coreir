#include "coreir/passes/transform/registerinputs.h"

using namespace std;
using namespace CoreIR;

bool Passes::RegisterInputs::runOnInstanceGraphNode(InstanceGraphNode& node) {

  Module* module = node.getModule();
  if (!module->hasDef()) return false;
  
  return false;
}
