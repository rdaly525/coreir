
#include "coreir-pass/passes.h"

using namespace std;
   
namespace CoreIR {

// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 
bool rungeneratorsRec(Context* c, Module* m, unordered_set<Module*>* ran);
void rungenerators(Context* c, Module* m, bool* err) {
  cout << "Running the Generators!" << endl;
  unordered_set<Module*> ran;
  *err = rungeneratorsRec(c,m,&ran);
  cout << "Done running the generators" << endl;
}


bool rungeneratorsRec(Context* c, Module* m, unordered_set<Module*>* ran) {
  
  //If I already checked module, then just return
  if (ran->count(m) > 0) return false;
  
  //If no definition, just return
  if (!m->hasDef()) return false; 

  // Check if there are runnable generators
  // Also insert all modules in the runQueue
  
  bool err = false;
  ModuleDef* mdef = m->getDef();
  for (auto instmap : mdef->getInstances() ) {
    Instance* inst = instmap.second;
    
    //If it is a generator, just run the generator
    if (inst->isGen()) {
      inst->runGenerator();
    }

    //run recursively on the module instance
    err |= rungeneratorsRec(c,inst->getModuleRef(),ran);
    
    //Test inlining
    //inst->inlineModule();
  }
  ran->insert(m);
  return err;
}

}//CoreIR namespace
