#include "coreir.h"

using namespace std;
using namespace CoreIR;


int main() {

  Context* c = newContext();
  Namespace* g = c->getGlobal();

  Type* mTp = c->Record({{"pad", c->BitInOut()},
        {"input", c->BitIn()},
          {"en", c->BitIn()}});
  Module* md = g->newModuleDecl("m", mTp);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("tb", "coreir.tribuf", {{"width", Const::make(c, 1)}});

  def->connect("self.en", "tb.en");
  def->connect("self.input", "tb.in.0");
  def->connect("tb.out.0", "self.pad");

  md->setDef(def);

  assert(md->getDef()->getInstances().size() == 1);

  c->runPasses({"deletedeadinstances"});

  assert(md->getDef()->getInstances().size() == 1);

  deleteContext(c);
}
