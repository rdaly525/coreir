#include "coreir.h"

using namespace CoreIR;
using namespace std;

int main() {

  // Note: I cant load rtlil here. Need to change build structure.

  Context* c = newContext();
  Namespace* g = c->getGlobal();

  Type* mTp = c->Record({{"inout1", c->BitInOut()},
        {"inout2", c->BitInOut()}});

  Module* m = g->newModuleDecl("m", mTp);
  ModuleDef* def = m->newModuleDef();

  deleteContext(c);
}
