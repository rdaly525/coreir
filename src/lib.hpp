#ifndef LIB_HPP_
#define LIB_HPP_


#include <iostream>
#include <string>
#include <map>
#include <vector>
#include "magmair.hpp"



bool Validate(Circuit* c) {

  // Circuit is valid if its interface and all its instances are _wired
  if(c->isPrimitive()) {
    cout << "Primitives are by definition valid!\n";
    return true;
  }
  bool valid = true;
  Module* mod = (Module*) c;
  if (!mod->getInterface()->checkWired()) {
    cout << "Inteface is Not fully connected!\n";
    return false;
  }
  vector<Instance*> insts = mod->getInstances();
  vector<Instance*>::iterator it;
  for(it=insts.begin(); it!=insts.end(); ++it) {
    if (!(*it)->checkWired() ) {
      cout << "Instance: " << (*it)->_string() << " is not fully connected\n";
      valid = false;
    }
  }
  cout << "You have a valid Module!\n";
  return valid;
}

void Unify(Wireable* w) {

}

// Takes a Wireable<T> and a Module<{inStr:~T, ,outStr:T}> 
void AddInstanceToWire(Wireable* w, Module m, string inStr, string outStr) {
  if(m->getType()->sel(inStr) != w->getType()->flip() && m->getType()->sel(outStr) != w->getType() ) {
    cout << "Types do not match!!\n";
  }
  Module* cont = w->getContainer();
  
}

// Replace instance with a module. (literally change the container pointer)

Module* Flatten(Module* mod) {
  if (inst->getCircuitType()->isPrimitive() ) return;

  Module* mod = inst->getContainer();
  string n = inst->_string();
  //For each child, instantiate the child
  // To name just use _ to connect
  vector<Instance*>::iterator it;
  vector<Instance*> instances = ((Module*)(inst->getCircuitType()))->getInstances();
  for (it=instances.begin(); it!=instances.end(); ++it) {
    //Instance each instance in mod
    Instance* oldInst = *it;
    Instance* newInst = mod->newInstance(n+oldInst->_string(),oldInst->getCircuitType());
    
  }
}

#endif //LIB_HPP_
