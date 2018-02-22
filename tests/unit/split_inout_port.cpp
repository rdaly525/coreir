#include "coreir.h"

using namespace CoreIR;
using namespace std;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  uint width = 1;
  
  Type* tp = c->Record({{"io", c->BitInOut()},
        {"en", c->BitIn()},
          {"from_io", c->Bit()},
            {"to_io", c->BitIn()}});

  Module* io = g->newModuleDecl("io", tp);
  ModuleDef* def = io->newModuleDef();

  def->addInstance("tristate_buf",
                   "coreir.triput",
                   {{"width", Const::make(c, width)}});

  def->addInstance("tristate_out",
                   "coreir.triget",
                   {{"width", Const::make(c, width)}});

  def->connect("tristate_buf.en", "self.en");
  def->connect("tristate_buf.in.0", "self.to_io");
  def->connect("tristate_buf.out.0", "self.io");

  def->connect("tristate_out.in.0", "self.io");
  def->connect("tristate_out.out.0", "self.from_io");

  io->setDef(def);

  cout << "Before splitting" << endl;
  io->print();

  c->runPasses({"split-inouts"});

  cout << "After splitting" << endl;
  io->print();

  assert(def->getInstances().size() == 1);

  deleteContext(c);
}
