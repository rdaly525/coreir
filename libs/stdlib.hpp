#ifndef STDLIB_HPP_
#define STDLIB_HPP_

#include "context.hpp"


Type* binop_type(CoreIRContext* c, GenArgs* args, ArgKinds kinds) {
  int n = c->toInt((*args)[0]);
  Type* narray = c->Array(n,c->BitOut());
  return c->Record({
      {"in0",c->Flip(narray)},
      {"in1",c->Flip(narray)},
      {"out",narray}
  });
}

Namespace* getStdlib(CoreIRContext* c) {
  
  Namespace* stdlib = c->newNamespace("stdlib");
  //c->registerLib(stdlib);

  //Add bop typegen to library
  stdlib->newTypeGen("binop","binop_F",{GINT},binop_type);
 
  //declare new add2 generator
  Generator* add2Gen = c->newGeneratorDecl("add2",{GINT},stdlib->getTypeGen("binop"));
  
  //Add Generator to library
  stdlib->addGenerator(add2Gen);
  
  return stdlib;
}


#endif //STDLIB_HPP_
