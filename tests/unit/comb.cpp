#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  // Type of module
  Type* addmultType = c->Record(
    {{"in", c->BitIn()->Arr(16)->Arr(3)}, {"out", c->Bit()->Arr(16)}});
  Values w16({{"width", Const::make(c, 16)}});
  Module* addmult = c->getGlobal()->newModuleDecl("addmult", addmultType);
  ModuleDef* def = addmult->newModuleDef();
  Constructor C(def);
  auto io = def->getInterface();
  auto add_out = C.add(io->sel("in")->sel(0), C.const_(16, 60));
  auto mul_out = C.mul(add_out, C.const_(16, 20));
  auto cat_out = C.concat(add_out, mul_out);
  auto cat2_out = C.concat(cat_out, io->sel("in")->sel(2));
  auto slice_out = C.slice(cat2_out, 23, 23 + 16);
  def->connect(slice_out, io->sel("out"));
  addmult->setDef(def);

  addmult->print();
  cout << addmult->toString() << endl;

  deleteContext(c);
  return 0;
}
