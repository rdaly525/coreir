#include "context.hpp"
#include <cassert>

using namespace CoreIR;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();

  assert(c->Any() == c->Any() );
  assert(c->Any() == c->Flip(c->Any()) );

  assert(c->BitIn() == c->BitIn());
  assert(c->BitOut() == c->BitOut());
  assert(c->BitIn() == c->Flip(c->BitOut()));



  // Test out TypeGens
  g->newTypeGen("int", "intIn", {{"w",GINT}}, NULL);
  //g->newTypeGen("intIn", "int", {GINT}, NULL);
  TypeGen* td1 = g->getTypeGen("int");
  TypeGen* td2 = g->getTypeGen("intIn");

  assert(td1 == td2->flipped);

  //TODO check a bunch more permutations
  //Check TypeGen
  GenArgs* ga1 = c->newGenArgs({{"w",c->GInt(3)}});
  GenArgs* ga2 = c->newGenArgs({{"w",c->GInt(3)}});
  GenArgs* ga3 = c->newGenArgs({{"w",c->GInt(4)}});
  GenArgs* ga4 = c->newGenArgs({{"w",c->GInt(2)}});
  
  assert(ga1 != ga2);
  assert(c->TypeGenInst(td1, ga1) == c->TypeGenInst(td1,ga2));
  assert(c->TypeGenInst(td1, ga1) != c->TypeGenInst(td1,ga3));
  assert(c->TypeGenInst(td1, ga1) != c->TypeGenInst(td1,ga4));
  assert(c->TypeGenInst(td1, ga3) != c->TypeGenInst(td1,ga4));
  
  assert(c->TypeGenInst(td1, ga1) == c->Flip(c->TypeGenInst(td2,ga1)));
  
  Type* Int = c->TypeGenInst(td1,ga1);
  vector<Type*> ts = {
    c->BitIn(),
    c->BitOut(),
    c->Array(5,c->BitIn()),
    c->Array(6,c->Array(7,c->BitOut())),
    c->Record({{"a",c->BitIn()},{"b",c->Array(8,c->BitOut())}}),
    c->TypeGenInst(td1, ga1),
    c->Record({{"r",c->Flip(Int)},{"v",Int},{"d",c->Array(16,Int)}})
  };
  for (auto t: ts) {
    assert(t == c->Flip(c->Flip(t)));
    assert(c->Array(5,t) == c->Array(5,t));
    assert(c->Array(5,t) != c->Array(6,t));
    assert(c->Flip(c->Array(7,t)) == c->Array(7,c->Flip(t)) );

    assert(c->Record({{"c",t}}) == c->Record({{"c",t}}) );
    //TODO more
  }
  deleteContext(c);

}
