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
  auto reg_out = C.reg(mul_out, 0);
  auto regarst_out = C.reg_arst(reg_out, 0);
  def->connect(regarst_out, io->sel("out"));
  addmult->setDef(def);

  addmult->print();
  cout << addmult->toString() << endl;

  deleteContext(c);
  return 0;
}
