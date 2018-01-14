#include "coreir.h"

#include "coreir/passes/transform/packbitconstants.h"

using namespace std;
using namespace CoreIR;

//Do not forget to set this static variable!!
string Passes::PackBitConstants::ID = "packbitconstants";
bool Passes::PackBitConstants::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  cout << "Processing module: " << m->getName() << endl;

  ModuleDef* def = m->getDef();

  for (auto instR : def->getInstances()) {
    Instance* inst = instR.second;

    for (auto selR : inst->getSelects()) {
      Select* sel = selR.second;

      if (isBitArray(*(sel->getType())) &&
          (sel->getType()->getDir() == Type::DK_In)) {
        cout << sel->toString() << " is input" << endl;
        vector<Select*> selSig = getSignalValues(sel);
        maybe<BitVec> sigValue = getSignalBitVec(selSig);

        if (sigValue.has_value()) {
          cout << "\t" << sel->toString() << " is fully connected to constants " << endl;
        }
      }
    }
  }

  return false;
}
