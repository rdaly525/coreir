#include "coreir.h"

using namespace CoreIR;
using namespace std;

int main() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();
  Type* tp = c->Record({{"in", c->BitIn()->Arr(3)},
        {"clk", c->Named("coreir.clkIn")},
          {"out", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("port_in", tp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("reg", "coreir.reg",
                   {{"width", Const::make(c, 3)}},
                   {{"init", Const::make(c, BitVec(3, 0))}});

  def->connect("self.in", "reg.in");
  def->connect("self.clk", "reg.clk");
  def->connect("reg.out", "self.out");

  md->setDef(def);

  assert(false);

  deleteContext(c);
}
