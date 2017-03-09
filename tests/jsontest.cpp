#include "context.hpp"
#include <cassert>
#include "passes.hpp"

#include <iostream>
#include <fstream>

int main() {
  Context* c = newContext();
  loadModule(c,"a.json");
  
  Module* m = c->newModuleDecl("ModTest",c->BitIn());
  saveModule(m,"b.json");
  deleteContext(c);
  return 0;
}
