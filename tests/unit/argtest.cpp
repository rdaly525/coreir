#include "coreir.h"
#include <cassert>

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  // TODO should test a bunch of other permutations
  Args g1 = {{"a",Const(5)},{"b",Const("ross")}};
  Args g2 = {{"a",Const(5)},{"b",Const("ross")}};
  Args g3 = {{"c",Const(5)},{"b",Const("ross")}};
  Args g4 = {{"a",Const(5)},{"b",Const("ross")},{"c",Const(c->BitIn())}};
  assert(g1 == g2);
  checkArgsAreParams(g1,{{"a",AINT},{"b",ASTRING}});
  assert(g1 != g3);
  assert(g1 != g4);
  checkArgsAreParams(g4,{{"a",AINT},{"b",ASTRING},{"c",ATYPE}});
  deleteContext(c);
  return 0;
}
