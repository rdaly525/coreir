#include "coreir.h"

#include "coreir/passes/transform/packconnections.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  Type* mTp = c->Record({{"input", c->BitIn()->Arr(3)},
                         {"out0", c->Bit()->Arr(3)},
                         {"out1", c->Bit()->Arr(3)}});

  Module* md = g->newModuleDecl("m", mTp);
  ModuleDef* def = md->newModuleDef();

  def->connect("self.input.0", "self.out0.0");
  def->connect("self.input.1", "self.out0.1");
  def->connect("self.input.2", "self.out0.2");

  def->connect("self.input.0", "self.out1.0");
  def->connect("self.input.1", "self.out1.1");
  def->connect("self.input.2", "self.out1.2");

  md->setDef(def);

  c->runPasses({"packconnections"});

  assert(def->getConnections().size() == 2);

  deleteContext(c);
}
