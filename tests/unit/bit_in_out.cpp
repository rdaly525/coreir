#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  Type* inTp = c->BitInOut();

  cout << "Bit in out = " << inTp->toString() << endl;

  Type* tp =
    c->Record({
        {"pad", c->BitInOut()},
          {"p2f", c->Bit()},
            {"f2p", c->BitIn()}
      });

  cout << tp->toString() << endl;

  Namespace* g = c->getGlobal();
  Module* md = g->newModuleDecl("io", tp);
  ModuleDef* def = md->newModuleDef();

  // TODO: Add casting and connections
  // def->connect("self.pad", "self.p2f");
  // def->connect("self.pad", "self.f2p");
  
  md->setDef(def);

  

  deleteContext(c);
}
