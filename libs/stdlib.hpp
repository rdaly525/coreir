#ifndef STDLIB_HPP_
#define STDLIB_HPP_

#include "context.hpp"


Type* binop_type(Context* c, GenArgs* args, GenParams kinds) {
  int n = c->toInt((*args)["w"]);
  Type* narray = c->Array(n,c->BitOut());
  return c->Record({
      {"in0",c->Flip(narray)},
      {"in1",c->Flip(narray)},
      {"out",narray}
  });
}

Namespace* getStdlib(Context* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
  //c->registerLib(stdlib);
  //Add bop typegen to library
  stdlib->newTypeGen("binop","binop_F",{{"w",GINT}},binop_type);
  
  //declare new add2 generator
  stdlib->newGeneratorDecl("add2",{{"w",GINT}},stdlib->getTypeGen("binop"));
  
  return stdlib;
}


#endif //STDLIB_HPP_
