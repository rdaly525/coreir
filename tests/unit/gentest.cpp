#include "context.hpp"
#include <cassert>

int main() {
  Context* c = newContext();

  // TODO should test a bunch of other permutations
  GenArgs g1 = *c->newGenArgs({{"a",c->GInt(5)},{"b",c->GString("ross")}});
  GenArgs g2 = *c->newGenArgs({{"a",c->GInt(5)},{"b",c->GString("ross")}});
  GenArgs g3 = *c->newGenArgs({{"c",c->GInt(5)},{"b",c->GString("ross")}});
  GenArgs g4 = *c->newGenArgs({{"a",c->GInt(5)},{"b",c->GString("ross")},{"c",c->GType(c->BitIn())}});
  assert(g1 == g2);
  assert(g1.checkKinds({{"a",GINT},{"b",GSTRING}}));
  assert(g1 != g3);
  assert(g1 != g4);
  assert(g4.checkKinds({{"a",GINT},{"b",GSTRING},{"c",GTYPE}}));
  deleteContext(c);
  return 0;
}
