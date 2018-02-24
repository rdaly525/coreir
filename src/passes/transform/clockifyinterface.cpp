#include "coreir.h"
#include "coreir/passes/transform/clockifyinterface.h"

using namespace std;
using namespace CoreIR;

//Do not forget to set this static variable!!

bool Passes::ClockifyInterface::runOnInstanceGraphNode(InstanceGraphNode& node) {

  Module* m = node.getModule();
  if (!m->hasDef()) {
    return false;
  }

  ModuleDef* def = m->getDef();
  Context* c = def->getContext();

  cout << "Processing module: " << m->getName() << endl;

  vector<Select*> possibleClocks;
  for (auto field : m->getType()->getRecord()) {
    if (field.second == c->BitIn()) {
      possibleClocks.push_back(def->sel("self")->sel(field.first));
    }
  }

  bool modifiedClock = false;
  for (auto pclk : possibleClocks) {
    bool allClocks = true;
    int numInputs = pclk->getConnectedWireables().size();

    for (auto sel : pclk->getConnectedWireables()) {

      //cout << pclk->toString() << " is connected to " << sel->toString() << endl;

      Select* selS = cast<Select>(sel);
      Wireable* parent = selS->getParent();

      if (!isa<Instance>(parent)) {
        cout << "NOT ALL CLOCKS: " << pclk->toString() << " connects to " << parent->toString() << ", which is not an instance" << endl;
        allClocks = false;
        break;
      } else {
        Instance* inst = cast<Instance>(parent);
        if (getQualifiedOpName(*inst) != "coreir.wrap") {

          cout << "NOT ALL CLOCKS: " << pclk->toString() << " connects to " << inst->toString() << ", which is not a wrap node" << endl;
          allClocks = false;
          break;
        } else {
          //cout << inst->toString() << " is a wrap node" << endl;

          // cout << "args" << endl;
          // for (auto arg : inst->getModArgs()) {
          //   cout << arg.first << " = " << arg.second->toString() << endl;
          // }

          auto arg = (inst->getModuleRef()->getGenArgs()).at("type")->get<Type*>();

          //cout << "Got arg = " << arg->toString() << endl;

          if (isa<NamedType>(arg)) {
            cout << arg->toString() << " is a named type" << endl;

            NamedType* ntp = cast<NamedType>(arg);

            //cout << "arg name = " << ntp->getName() << endl;

            if (ntp->getRefName() != "coreir.clk") {

              cout << "NOT ALL CLOCKS: " << pclk->toString() << " connects to " << inst->toString() << ", which casts to type " << ntp->toString() << endl;
              allClocks = false;
              break;
            }
          } else {
            cout << "NOT ALL CLOCKS: " << pclk->toString() << " connects to " << inst->toString() << ", which casts to type " << arg->toString() << endl;
            allClocks = false;
            break;
          }
        }
      }
    }

    if (allClocks && (numInputs > 0)) {
      cout << "All receivers of " << pclk->toString() << " are clock casts" << endl;

      // Now need to:
      // 1. Delete original BitIn field from interface type
      // 2. Add new clock field to interface type
      // 3. Connect the new clock field to every receiver of every wrap cast

      // Collect every reciever port that the new clock port in the interface
      // will connect to
      vector<Wireable*> connectToNewClock;
      for (auto sel : pclk->getConnectedWireables()) {
        Instance* inst = cast<Instance>(cast<Select>(sel)->getParent());
        Select* outConn = inst->sel("out");

        // Need to build receiver map and use it here
        for (auto receiverPort : outConn->getConnectedWireables()) {
          cout << "\t" << receiverPort->toString() <<
            " connects to " << outConn->toString() << endl;

          connectToNewClock.push_back(receiverPort);
        }
      }

      // Delete all cast instances that are no longer needed
      vector<Instance*> toDelete;
      for (auto sel : pclk->getConnectedWireables()) {
        Instance* inst = cast<Instance>(cast<Select>(sel)->getParent());
        toDelete.push_back(inst);
      }
      for (auto inst : toDelete) {
        def->removeInstance(inst);
      }

      string clkFieldName = pclk->getSelStr();
      node.detachField(clkFieldName);

      node.appendField(clkFieldName, c->Named("coreir.clkIn"));

      Select* s = def->sel("self")->sel(clkFieldName);

      // Wire the new clock port to all old connections
      for (auto w : connectToNewClock) {
        def->connect(s, w);
      }
      
      modifiedClock = true;
    }
  }

  return modifiedClock;
}
