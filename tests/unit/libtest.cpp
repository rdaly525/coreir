#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  // New context
  Context* c = newContext();
  
  Namespace* g = c->getGlobal();
  
  c->getLibraryManager()->loadLib("commonlib");

  Module* test = g->newModuleDecl("Add4",c->Record({}));
  ModuleDef* def = test->newModuleDef();
    
    def->addInstance("i0","commonlib.smax",{{"width",Const::make(c,17)}});
  test->setDef(def);
  test->print();

  deleteContext(c);
  
  return 0;
}
