#include "coreir.h"
#include "coreir/passes/transform/cullzexts.h"

using namespace std;
using namespace CoreIR;

string Passes::CullZexts::ID = "cullzexts";

bool Passes::CullZexts::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  auto def = m->getDef();

  bool deletedZext = false;
  for (auto instS : def->getInstances()) {
    Instance* inst = instS.second;

    if (getQualifiedOpName(*inst) == "coreir.zext") {
      auto args = inst->getModuleRef()->getGenArgs();

      uint in_width = args.at("width_in")->get<int>();
      uint out_width = args.at("width_out")->get<int>();

      if (in_width == out_width) {
        // Found useless zext
        cout << inst->toString() << " is an identity zext" << endl;

        Select* inSel = inst->sel("in");
        Select* outSel = inst->sel("out");

        // Only handling easy wiring case for now
        if ((inSel->getConnectedWireables().size() == 1) &&
            (outSel->getConnectedWireables().size() == 1)) {

          cout << "Deleting " << inst->toString() << endl;

          Select* toIn = cast<Select>(*std::begin(inSel->getConnectedWireables()));
          Select* toOut = cast<Select>(*std::begin(outSel->getConnectedWireables()));

          def->removeInstance(inst);

          def->connect(toIn, toOut);

          deletedZext = true;
        }
      }
    }
  }

  return deletedZext;
}
