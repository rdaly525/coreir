#include "coreir/passes/transform/registerinputs.h"

using namespace std;
using namespace CoreIR;

bool Passes::RegisterInputs::runOnInstanceGraphNode(InstanceGraphNode& node) {

  Module* module = node.getModule();
  if (!module->hasDef()) {
    return false;
  }

  Context* c = module->getDef()->getContext();
  for (auto& field : module->getType()->getRecord()) {
    if (field.second != c->Named("coreir.clkIn")) {
      cout << "Input = " << field.first << endl;
    }
  }
  
  return false;
}
