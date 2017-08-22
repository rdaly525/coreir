
/*
 * Make sure you start at hellomodule.hpp before this one.
 *
 * This is just filling out some function definitions
 */

#include "coreir.h"
#include "hellomodule.hpp"

//This is For a convenient macro to create the registerPass and deletePass functions
#include "coreir-macros.h"

using namespace CoreIR;


//Do not forget to set this static variable!!
string HelloModule::ID = "hellomodule";
bool HelloModule::runOnModule(Module* m) {
  Context* c = this->getContext();

  //The ModulePass runs on Modules whether or not they are a declaration or a definition.
  //since this pass only cares about finding registers, we early-out on the declarations
  if (!m->hasDef()) return false;

  ModuleDef* def = m->getDef();
  
  //Get the insantiable which we want to compare against
  //Note this will do an automatic upcast which is fine
  Instantiable* coreir_reg = c->getGenerator("coreir.reg");

  
  //Define our vecotr of instances
  vector<Instance*> regInsts;
  //Loop through all the instances 
  for (auto instmap : def->getInstances()) {
    Instance* inst = instmap.second;
    
    //If the instance's InstantiableRef (the thing that it is instancing) is a coreir.reg
    //increment the counter
    if (inst->getInstantiableRef() == coreir_reg) {
      regInsts.push_back(inst);
    }
  }
  //Add this current module to the user datastructure we defined before
  if (regInsts.size() > 0 ) {
    registerMap[m] = regInsts;
  }
  return false;
}

//Just filling out the function bodies. 
bool HelloModule::hasRegisterInstances(Instantiable* i) {
  return registerMap.count(i) > 0;
}

std::vector<Instance*> HelloModule::getRegisterInstances(Instantiable* i) {
  //A little unsafe because this adds wrong Instances to the reigster map.
  return registerMap[i];
}

//Just filling out the function bodies. 
int HelloModule::getTotalRegisters() {
  int total = 0;
  for (auto rmap : registerMap) {
    total += rmap.second.size();
  }
  return total;
}

void HelloModule::print() {
  cout << "Total number of registers is: " << this->getTotalRegisters() << endl;
}

//This is the macro that will define the registerPass and deletePass functions for you.
COREIR_GEN_EXTERNAL_PASS(HelloModule);
