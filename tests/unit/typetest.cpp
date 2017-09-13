#include "coreir.h"
#include <cassert>

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  // Basic invarients of Any and BitIn
  assert(c->Any() == c->Any() );
  assert(c->Any() == c->Flip(c->Any()) );

  assert(c->BitIn() == c->BitIn());
  assert(c->Bit() == c->Bit());
  assert(c->BitIn() == c->Flip(c->Bit()));


  // Test out Named Types
  g->newNamedType("int16","intIn16",c->Array(16,c->Bit()));
  assert(g->getNamedType("int16") == c->Flip(g->getNamedType("intIn16")));

  auto intTypeFun = [](Context* c, Args args) {
    int n = args.at("w")->get<ArgInt>();
    return c->Array(n,c->Bit());
  };

  g->newNominalTypeGen("int", "intIn",{{"w",AINT}},intTypeFun);
  Args ga1 = {{"w",c->argInt(16)}};
  Args ga2 = {{"w",c->argInt(16)}};
  Args ga3 = {{"w",c->argInt(17)}};
  
  ASSERT(ga1 == ga2,"Equality is bad");
  ASSERT(ga1 != ga3,"not equalit is bad");
  assert(g->getNamedType("int",ga1) == g->getNamedType("int",ga2));
  assert(g->getNamedType("int",ga1) != g->getNamedType("int",ga3));
  assert(g->getNamedType("int",ga1) == c->Flip(g->getNamedType("intIn",ga2)));
  assert(g->getNamedType("int",ga1) != c->Flip(g->getNamedType("intIn",ga3)));
  
  Type* Inta = g->getNamedType("int16");
  Type* Intb = g->getNamedType("int",ga1);
  vector<Type*> ts = {
    c->BitIn(),
    c->Bit(),
    c->Array(5,c->BitIn()),
    c->Array(6,c->Bit())->Arr(5)->Arr(3)->Arr(2),
    c->Record({{"a",c->BitIn()},{"b",c->Array(8,c->Bit())}}),
    Inta,
    Intb,
    c->Record({{"r",c->Flip(Inta)},{"v",Intb},{"d",c->Array(16,Inta)}})
  };
  for (auto t: ts) {
    assert(t == c->Flip(c->Flip(t)));
    assert(c->Array(5,t) == c->Array(5,t));
    assert(c->Array(5,t) != c->Array(6,t));
    assert(c->Flip(c->Array(7,t)) == c->Array(7,c->Flip(t)) );
    assert(c->Record({{"c",t}}) == c->Record({{"c",t}}) );
    t->print();
  }
  deleteContext(c);

}
