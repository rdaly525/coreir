#include "coreir.h"
#include <cassert>

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  // TODO should test a bunch of other permutations
  Values g1 = {{"a",Const::make(c,5)},{"b",Const::make(c,"ross")}};
  Values g2 = {{"a",Const::make(c,5)},{"b",Const::make(c,"ross")}};
  Values g3 = {{"c",Const::make(c,5)},{"b",Const::make(c,"ross")}};
  Values g4 = {{"a",Const::make(c,5)},{"b",Const::make(c,"ross")},{"c",Const::make(c,c->BitIn())}};
  assert(g1 == g2);
  checkValuesAreParams(g1,{{"a",c->Int()},{"b",c->String()}});
  assert(g1 != g3);
  assert(g1 != g4);
  checkValuesAreParams(g4,{{"a",c->Int()},{"b",c->String()},{"c",c->CoreIRType()}});
  deleteContext(c);
  return 0;
}
