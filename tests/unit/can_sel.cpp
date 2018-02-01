#include "coreir.h"

#include <string>
#include <fstream>
#include <streambuf>

#include "coreir/libs/rtlil.h"
#include "coreir/passes/transform/deletedeadinstances.h"
#include "coreir/passes/transform/unpackconnections.h"
#include "coreir/passes/transform/packconnections.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* g = c->getGlobal();

  uint width = 4;

  Type* addModTP = c->Record({
      {"in0", c->BitIn()->Arr(width)},
        {"in1", c->BitIn()->Arr(width)},
          {"out", c->Bit()->Arr(width)}
    });

  Module* addMod = g->newModuleDecl("addMod", addModTP);
  ModuleDef* def = addMod->newModuleDef();

  def->addInstance("add0", "coreir.add", {{"width", Const::make(c, width)}});

  def->connect("self.in0", "add0.in0");
  def->connect("self.in1", "add0.in1");

  def->connect("add0.out.0", "self.out.0");
  def->connect("add0.out.1", "self.out.1");
  def->connect("add0.out.2", "self.out.2");
  def->connect("add0.out.3", "self.out.3");

  addMod->setDef(def);

  cout << "addMod" << endl;
  addMod->print();

  assert(addMod->getDef()->canSel("self.out"));

  // Q: What is the appropriate behavior here? No such select? Say this select
  //    exists?
  assert(addMod->getDef()->canSel("self.out.0"));

  deleteContext(c);
}
