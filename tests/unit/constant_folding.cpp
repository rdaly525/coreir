#include "coreir.h"

#include "coreir/libs/rtlil.h"
#include "coreir/passes/transform/deletedeadinstances.h"
#include "coreir/passes/transform/unpackconnections.h"
#include "coreir/passes/transform/packconnections.h"

using namespace std;
using namespace CoreIR;

void testFoldEquals() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  uint width = 2;

  Type* eqModTP = c->Record({{"out", c->Bit()}});

  Module* eqMod = g->newModuleDecl("eqMod", eqModTP);
  ModuleDef* def = eqMod->newModuleDef();

  def->addInstance("cmp", "coreir.eq", {{"width", Const::make(c, width)}});

  def->addInstance("c0", "coreir.const", {{"width", Const::make(c, width)}}, {{"value", Const::make(c, BitVec(width, 4))}});

  def->addInstance("c1", "coreir.const", {{"width", Const::make(c, width)}}, {{"value", Const::make(c, BitVec(width, 4))}});

  def->connect("c0.out.0", "cmp.in0.0");
  def->connect("c0.out.1", "cmp.in0.1");

  def->connect("c1.out.0", "cmp.in1.0");
  def->connect("c1.out.1", "cmp.in1.1");

  def->connect("cmp.out", "self.out");
  
  eqMod->setDef(def);

  foldConstants(eqMod);
  deleteDeadInstances(eqMod);

  cout << "eqMod after folding constants" << endl;
  eqMod->print();

  assert(eqMod->getDef()->getInstances().size() == 1);

  deleteContext(c);
}

int main() {
  testFoldEquals();
}
