#include "coreir.h"
#include "coreir/passes/transform/clockifyinterface.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::ClockifyInterface::ID = "clockifyinterface";
bool Passes::ClockifyInterface::runOnModule(Module* m) {
  if (!m->hasDef()) {
    return false;
  }

  ModuleDef* def = m->getDef();
  Context* c = def->getContext();

  cout << "Processing module: " << m->getName() << endl;

  Wireable* topclk = nullptr;
  for (auto field : m->getType()->getRecord()) {
    if (field.second == c->BitIn()) {
      topclk = def->sel("self")->sel(field.first);
    }
  }

  return true;
}
