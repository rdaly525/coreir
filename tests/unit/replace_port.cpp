#include "coreir.h"

using namespace CoreIR;
using namespace std;

int main() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()->Arr(3)},
        {"out", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("neg", "coreir.not", {{"width", Const::make(c, 3)}});
  def->connect("self.in", "neg.in");
  def->connect("neg.out", "self.out");

  md->setDef(def);

  portToConstant("in", BitVec(3, 5), md);

  cout << "module after" << endl;
  md->print();

  SimulatorState state(md);
  state.execute();

  cout << "self.out      = " << state.getBitVec("self.out") << endl;
  cout << "~BitVec(3, 5) = " << ~BitVec(3, 5) << endl;

  assert(state.getBitVec("self.out") == ~BitVec(3, 5));

  deleteContext(c);

  assert(false);
}
