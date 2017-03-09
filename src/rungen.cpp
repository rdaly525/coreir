#ifndef COMPILER_CPP_
#define COMPILER_CPP_

#include "common.hpp"
#include "passes.hpp"

using namespace std;
   
// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 
bool rungeneratorsRec(Context* c, Module* m, set<Module*>* ran);
bool rungenerators(Context* c, Module* m) {
  cout << "Running the Generators" << endl;
  set<Module*> ran;
  bool err = rungeneratorsRec(c,m,&ran);
  cout << "Done running the generators" << endl;
  return err;
}


bool rungeneratorsRec(Context* c, Module* m, set<Module*>* ran) {
  
  //If I already ran, then just return
  if (ran->count(m) > 0) return false;
  //If no definition, just return
  if (!m->hasDef()) return false; 

  // Check if there are runnable generators
  // Also insert all modules in the runQueue
  set<Module*> runQueue;
  bool hasgens = false;
  ModuleDef* mdef = m->getDef();
  for (auto inst : mdef->getInstances() ) {
    if (inst->getInstRef()->isKind(MOD)) {
      runQueue.insert((Module*) inst->getInstRef());
    }
    else {
      Generator* g = (Generator*) inst->getInstRef();
      if (g->hasDef()) {
        hasgens = true;
        break;
      }
    }
  }
  
  bool err = false;

  // If there are no runnable generators, then we are done
  if (!hasgens) return false;

  // This means there are runnable generators;
  // I will need to construct a new moduleDef
  ModuleDef* newDef = m->newModuleDef();
  
  //maintain a map from old IFACE/INST to new ones
  unordered_map<Wireable*,Wireable*> old2new;
  
  //create new IFACE and INST and add to map
  // If the INST is a generator and has a def, then run it first
  old2new.emplace(mdef->getInterface(),newDef->getInterface());
  for (auto inst : mdef->getInstances() ) {
    if( inst->getInstRef()->isKind(MOD)) {
      old2new.emplace(inst,newDef->addInstance(inst));
    }
    else {
      Generator* g = (Generator*) inst->getInstRef();
      if (!g->hasDef()) {
        old2new.emplace(inst,newDef->addInstance(inst));
      }
      else {

        GenArgs* gargs = inst->getGenArgs();
        Module* mNew = c->getGlobal()->runGenerator(g,gargs);
        
        // TODO might not need to insert already cached things
        //Add Output of generator to runQueue
        runQueue.insert(mNew);
        
        //Create new instance and add to map
        old2new.emplace(inst,newDef->addInstanceModule(inst->getInstname(), mNew));
      }
    }
  }

  //Add all the wires to the new module def
  for (auto wire : mdef->getWires() ) {
    std::pair<Wireable*,vector<string>> serA = wire.first->serialize();
    std::pair<Wireable*,vector<string>> serB = wire.second->serialize();
    assert(old2new.count(serA.first)==1);
    assert(old2new.count(serB.first)==1);
    Wireable* curA = old2new[serA.first];
    Wireable* curB = old2new[serB.first];
    for (auto str : serA.second) curA = curA->sel(str);
    for (auto str : serB.second) curB = curB->sel(str);
    newDef->wire(curA,curB);
  }
  
  //Replace the module definition with this new one
  m->replaceDef(newDef);
  ran->insert(m);

  //recurively run through the runQueue
  for (auto mod : runQueue) {
    err |= rungeneratorsRec(c,mod,ran);
    ran->insert(mod);
  }


  return err;
}

#endif //COMPILER_CPP_
