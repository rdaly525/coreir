#include "coreir.h"
#include <cassert>

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  // Basic invarients of Bit/BitIn
  assert(c->BitIn() == c->BitIn());
  assert(c->Bit() == c->Bit());
  assert(c->BitIn() == c->Flip(c->Bit()));
  
  assert(c->BitInOut() == c->Flip(c->BitInOut()));
  assert(c->BitInOut()->Arr(5) == c->Flip(c->BitInOut()->Arr(5)));
  assert(c->Record({{"a",c->BitInOut()}}) == c->Flip(c->Record({{"a",c->BitInOut()}})));


  // Test out Named Types
  g->newNamedType("int16","intIn16",c->Array(16,c->Bit()));
  assert(g->getNamedType("int16") == c->Flip(g->getNamedType("intIn16")));

  //auto intTypeFun = [](Context* c, Values args) {
  //  int n = args.at("w")->get<int>();
  //  return c->Array(n,c->Bit());
  //};

  //g->newNominalTypeGen("int", "intIn",{{"w",c->Int()}},intTypeFun);
  //Values ga1 = {{"w",Const::make(c,16)}};
  //Values ga2 = {{"w",Const::make(c,16)}};
  //Values ga3 = {{"w",Const::make(c,17)}};
  //
  //ASSERT(ga1 == ga2,"Equality is bad");
  //ASSERT(ga1 != ga3,"not equalit is bad");
  //assert(g->getNamedType("int",ga1) == g->getNamedType("int",ga2));
  //assert(g->getNamedType("int",ga1) != g->getNamedType("int",ga3));
  //assert(g->getNamedType("int",ga1) == c->Flip(g->getNamedType("intIn",ga2)));
  //assert(g->getNamedType("int",ga1) != c->Flip(g->getNamedType("intIn",ga3)));
  //
  //Type* Inta = g->getNamedType("int16");
  //Type* Intb = g->getNamedType("int",ga1);
  vector<Type*> ts = {
    c->BitIn(),
    c->Bit(),
    c->BitInOut(),
    c->Array(5,c->BitIn()),
    c->Array(6,c->Bit())->Arr(5)->Arr(3)->Arr(2),
    c->BitInOut()->Arr(13),
    c->Record({{"a",c->BitIn()},{"b",c->Array(8,c->Bit())}})
    //Inta,
    //Intb,
    //c->Record({{"r",c->Flip(Inta)},{"v",Intb},{"d",c->Array(16,Inta)}})
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
