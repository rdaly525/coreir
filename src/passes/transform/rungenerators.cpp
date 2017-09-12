#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"

using namespace CoreIR;


// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 
bool rungeneratorsRec(Module* m, unordered_set<Module*>& ran, unordered_set<Module*>& toRelease) {
  assert(m);
  //If I already checked module, then just return
  if (ran.count(m) > 0) return false;

  // Check if there are runnable generators
  // Also insert all modules in the runQueue
  bool changed = false;
  ModuleDef* mdef = m->getDef();
  for (auto instmap : mdef->getInstances() ) {
    Instance* inst = instmap.second;
    
    //If it is a generator, just run the generator
    if (inst->isGen()) {
      if (inst->runGenerator()) {
        assert(!inst->isGen());
        assert(inst->wasGen());
        toRelease.insert(inst->getModuleRef());
        //run recursively on the module instance
        rungeneratorsRec(inst->getModuleRef(),ran,toRelease);
        changed = true;
      }
    }

  }
  ran.insert(m);
  return changed;
}

string Passes::RunGenerators::ID = "rungenerators";
bool Passes::RunGenerators::runOnNamespace(Namespace* ns) {
  //Keep list of modules to be added
  unordered_set<Module*> ran;
  unordered_set<Module*> toRelease;
  bool changed = false;
  for (auto mmap : ns->getModules()) {
    changed |= rungeneratorsRec(mmap.second,ran,toRelease);
  }

  //Now that all generators have run. Change module linking type for those
  //newly created instances to be namespace
  for (auto m : toRelease) {
    ns->addModule(m);
  }

  return changed;
}

