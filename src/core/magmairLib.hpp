#ifndef LIB_HPP_
#define LIB_HPP_


#include <iostream>
#include <string>
#include <map>
#include <vector>
#include "magmair.hpp"




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
