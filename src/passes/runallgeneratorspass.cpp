#include "coreir.h"
#include "coreir-passes/runallgeneratorspass.hpp"

using namespace CoreIR;


// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 
bool rungeneratorsRec(Module* m, unordered_set<Module*>& ran) {
  
  //If I already checked module, then just return
  if (ran.count(m) > 0) return false;
  
  //If no definition, just return
  if (!m->hasDef()) {
    ran.insert(m);
    return false; 
  }

  // Check if there are runnable generators
  // Also insert all modules in the runQueue
  bool changed = false;
  ModuleDef* mdef = m->getDef();
  for (auto instmap : mdef->getInstances() ) {
    Instance* inst = instmap.second;
    
    //If it is a generator, just run the generator
    if (inst->isGen()) {
      changed |= inst->runGenerator();
    }

    //run recursively on the module instance
    changed |= rungeneratorsRec(inst->getModuleRef(),ran);
  }
  ran.insert(m);
  return changed;
}

bool RunAllGeneratorsPass::runOnNamespace(Namespace* ns) {
  //Keep list of modules to be added
  unordered_set<Module*> ran;
  bool changed = false;
  for (auto mmap : ns->getModules()) {
    changed |= rungeneratorsRec(mmap.second,ran);
  }
  return changed;
}

