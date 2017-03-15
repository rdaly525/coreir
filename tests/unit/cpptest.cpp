
#include "coreir.h"
#include "context.hpp"

using namespace CoreIR;

int main() {
  
  
  Context* c = newContext();
  Type* bitIn = c->BitIn();
  Namespace* ns = c->getGlobal();
  Module* m = ns->newModuleDecl("Add8",bitIn);
  m->print();
  cout << "Trying to delete context" << endl;
  deleteContext(c);
  
  return 0;
}
