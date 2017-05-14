
#include "coreir-pass/passes.h"

using namespace std;
   
namespace CoreIR {

// This will inline all instances from the top
void flatten(Context* c, Module* m, bool* err) {
  cout << "flattening!" << endl;
  ModuleDef* def = m->getDef();
  bool inlined = true;
  while (inlined) {
    inlined = false;
    for (auto instmap : def->getInstances()) {
      //Only inline things in global
      if (instmap.second->getModuleRef()->getNamespace()->getName() == "_G") {
        instmap.second->inlineModule();
        inlined = true;
      }
    }
  }
  *err = false;
}

}//CoreIR namespace
