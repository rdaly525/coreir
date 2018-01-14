#include "coreir.h"
#include "coreir/passes/transform/packbitconstants.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::PackBitConstants::ID = "packBitConstants";
bool Passes::PackBitConstants::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  cout << "Processing module: " << m->getName() << endl;

  ModuleDef* def = m->getDef();

  return false;
}
