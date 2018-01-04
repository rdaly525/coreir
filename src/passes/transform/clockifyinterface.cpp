#include "coreir.h"
#include "coreir/passes/transform/clockifyinterface.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::Clockifyinterface::ID = "clockifyinterface";
bool Passes::Clockifyinterface::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  cout << "Processing module: " << m->getName() << endl;

  ModuleDef* def = m->getDef();

  return true;
}
