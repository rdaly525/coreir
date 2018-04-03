#include "coreir.h"
#include "coreir/passes/transform/delete_unused_inouts.h"

using namespace std;
using namespace CoreIR;

bool Passes::DeleteUnusedInouts::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* module = node.getModule();

  if (!module->hasDef()) {
    return false;
  }

  cout << "Processing module = " << module->getName() << endl;
  
  bool changed = false;
  
  map<Select*, Select*> inoutsToOuts;
  map<Select*, Select*> inoutsToIns;
  for (auto field : module->getType()->getRecord()) {
    if (field.second->getDir() == Type::DK_InOut) {
      string portName = field.first;

      Wireable* self = module->getDef()->sel("self");

      Select* ioPort = self->sel(portName);

      vector<Select*> ios = getIOSelects(ioPort);

      if (ios.size() == 0) {
        changed = true;
        node.detachField(portName);
      }

    }
  }
  
  return changed;
}
