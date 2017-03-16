#include "context.hpp"
#include <cassert>

using namespace CoreIR;

int main() {
  Context* c = newContext();

  // TODO should test a bunch of other permutations
  Args g1 = *c->args({{"a",c->int2Arg(5)},{"b",c->string2Arg("ross")}});
  Args g2 = *c->args({{"a",c->int2Arg(5)},{"b",c->string2Arg("ross")}});
  Args g3 = *c->args({{"c",c->int2Arg(5)},{"b",c->string2Arg("ross")}});
  Args g4 = *c->args({{"a",c->int2Arg(5)},{"b",c->string2Arg("ross")},{"c",c->type2Arg(c->BitIn())}});
  assert(g1 == g2);
  assert(g1.checkParams({{"a",AINT},{"b",ASTRING}}));
  assert(g1 != g3);
  assert(g1 != g4);
  assert(g4.checkParams({{"a",AINT},{"b",ASTRING},{"c",ATYPE}}));
  deleteContext(c);
  return 0;
}
