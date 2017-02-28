#include "context.hpp"
#include <cassert>

int main() {
  CoreIRContext* c = newContext();
  
  GenArgs g1 = GenArgs(2,{c->GInt(5), c->GString("ross")});
  GenArgs g2 = GenArgs(2,{c->GInt(5), c->GString("ross")});
  GenArgs g3 = GenArgs(3,{c->GInt(5), c->GString("ross"), c->GType(c->BitIn())});
  GenArgs g4 = GenArgs(3,{c->GInt(5), c->GString("ross"), c->GType(c->BitIn())});
  assert(g1 == g2);
  assert(g1.checkKinds({GINT,GSTRING}));
  assert(g1 != g3);
  assert(g3 == g4);
  assert(g3.checkKinds({GINT,GSTRING,GTYPE}));

  return 0;
}
