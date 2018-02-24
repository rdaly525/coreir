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
  def->connect("self.input", "tb.in");
  def->connect("tb.out", ,"self.pad");

  md->setDef(def);

  c->runPasses({"deletedeadinstances"});

  assert(md->getDef()->getInstances().size() == 1);

  assert(false);

  deleteContext(c);
}
