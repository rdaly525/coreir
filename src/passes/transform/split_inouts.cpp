#include "coreir.h"
#include "coreir/passes/transform/split_inouts.h"

using namespace std;
using namespace CoreIR;

bool Passes::SplitInouts::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* module = node.getModule();

  if (!module->hasDef()) {
    return false;
  }

  Context* c = module->getDef()->getContext();
  
  map<Select*, Select*> inoutsToOuts;
  map<Select*, Select*> inoutsToIns;
  for (auto field : module->getType()->getRecord()) {
    if (field.second->getDir() == Type::DK_InOut) {
      // TODO: Actually change the underlying array type instead
      // of just assuming its BitInOut
      string portName = field.first;
      string input = portName + "_input";
      string output = portName + "_output";

      node.appendField(input, c->Bit());
      node.appendField(output, c->BitIn());

      Wireable* self = module->getDef()->sel("self");

      Select* ioPort = self->sel(portName);
      Select* inputPort = self->sel(input);
      Select* outputPort = self->sel(output);

      cout << ioPort->toString() << endl;
      cout << inputPort->toString() << endl;
      cout << outputPort->toString() << endl;

      auto def = module->getDef();
      int width = 1;
      auto mux = def->addInstance(portName + "_split_mux",
                                  "coreir.mux",
                                  {{"width", Const::make(c, width)}});

      // Add array connections
      def->connect(mux->sel("in0")->sel(0), outputPort);
    }
  }
  return false;
}
