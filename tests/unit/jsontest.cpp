#include "context.hpp"
#include <cassert>

#include <iostream>
#include "stdlib.hpp"

int main() {
  Context* c = newContext();

  Namespace* stdlib = getStdlib(c);
  
  bool err = false;
  Module* m = loadModule(c,"add.json", &err);
  if(err) {
    c->die();
  }
  m->print();

  deleteContext(c);
  return 0;
}
