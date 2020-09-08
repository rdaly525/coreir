#include "coreir/passes/transform/unresolvedsymbols.h"
#include "coreir.h"

using namespace std;
using namespace CoreIR;

bool Passes::UnresolvedSymbols::runOnContext(Context* c) {
  cout << "NEW THING!" << endl;
  set<Module*> toErase;
  for (auto npair : c->getNamespaces()) {
    for (auto mpair : npair.second->getModules()) {
      Module* m = mpair.second;
      if (m->hasDef()) { toErase.insert(m); }
    }
  }
  for (auto m : toErase) {
    if (m->isGenerated()) { m->getGenerator()->eraseModule(m->getGenArgs()); }
    else {
      m->getNamespace()->eraseModule(m->getName());
    }
  }
  if (c->hasTop()) {
    c->removeTop();
    ASSERT(!c->hasTop(), "BAD!");
    return true;
  }
  ASSERT(!c->hasTop(), "BAD!");

  return toErase.size() > 0;
}
