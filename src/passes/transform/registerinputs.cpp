#include "coreir/passes/transform/registerinputs.h"

using namespace std;
using namespace CoreIR;

bool Passes::RegisterInputs::runOnInstanceGraphNode(InstanceGraphNode& node) {

  Module* module = node.getModule();
  if (!module->hasDef()) {
    return false;
  }

  ModuleDef* def = module->getDef();

  Context* c = module->getDef()->getContext();
  for (auto& field : module->getType()->getRecord()) {
    if (field.second != c->Named("coreir.clkIn")) {

      Type::DirKind dk = field.second->getDir();

      if (dk == Type::DirKind::DK_In) {
        //Wireable* w = field.first;
        cout << "Input = " << field.first << endl;

        // cout << "With connections" << endl;
        // for (auto& connected : w->getConnectedWireables()) {
        //   cout << connected->toString() << endl;
        // }
      }
    }
  }

  auto interface = def->getInterface();
  cout << interface->getType()->toString() << endl;

  cout << "# of wireables connected to interfaces = " << interface->getConnectedWireables().size() << endl;
  for (auto& wd : interface->getConnectedWireables()) {
    cout << wd->toString() << endl;
  }

  Wireable* self = def->sel("self");
  cout << "# of wireables connected to self = " << self->getConnectedWireables().size() << endl;
  for (auto& wd : self->getConnectedWireables()) {
    cout << wd->toString() << endl;
  }

  map<Wireable*, Instance*> newRegs;
  for (auto& conn : def->getConnections()) {
    cout << Connection2Str(conn) << endl;

    // Wireable* sel1 = conn.first;
    // Wireable* sel2 = conn.second;

    
  }
  
  return true;
}
