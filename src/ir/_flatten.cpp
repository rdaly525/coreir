
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
    //TODO Not sure why this is not segfaulting
    for (auto instmap : def->getInstances()) {
      //Only inline things that have defs
      if (instmap.second->getModuleRef()->hasDef()) {
        inlineInstance(instmap.second);
        inlined = true;
      }
    }
  }
  *err = false;
}

}//CoreIR namespace
