
/*
 * Make sure you start at hellomodule.h before this one.
 *
 * This is just filling out some function definitions
 */

#include "coreir.h"
#include "coreir/passes/analysis/hellomodule.h"

using namespace std;
using namespace CoreIR;


//Do not forget to set this static variable!!
string Passes::HelloModule::ID = "hellomodule2";
bool Passes::HelloModule::runOnModule(Module* m) {
  Context* c = this->getContext();

  //The ModulePass runs on Modules whether or not they are a declaration or a definition.
  //since this pass only cares about finding registers, we early-out on the declarations
  if (!m->hasDef()) return false;

  ModuleDef* def = m->getDef();
  
  //Get the insantiable which we want to compare against
  //Note this will do an automatic upcast which is fine
  Generator* coreir_reg = c->getGenerator("coreir.reg");

  
  //Define our vecotr of instances
  vector<Instance*> regInsts;
  //Loop through all the instances 
  for (auto instmap : def->getInstances()) {
    Instance* inst = instmap.second;
    
    //If the instance's InstantiableRef (the thing that it is instancing) is a coreir.reg
    //increment the counter
    if (inst->getModuleRef()->isGenerated()) {
      if (inst->getModuleRef()->getGenerator() == coreir_reg) {
        regInsts.push_back(inst);
      }
    }
  }
  //Add this current module to the user datastructure we defined before
  if (regInsts.size() > 0 ) {
    registerMap[m] = regInsts;
  }
  return false;
}

//Just filling out the function bodies. 
bool Passes::HelloModule::hasRegisterInstances(Module* m) {
  return registerMap.count(m) > 0;
}

std::vector<Instance*> Passes::HelloModule::getRegisterInstances(Module* m) {
  //A little unsafe because this adds wrong Instances to the reigster map.
  return registerMap[m];
}

//Just filling out the function bodies. 
int Passes::HelloModule::getTotalRegisters() {
  int total = 0;
  for (auto rmap : registerMap) {
    total += rmap.second.size();
  }
  return total;
}

void Passes::HelloModule::print() {
  cout << "Total number of registers is: " << this->getTotalRegisters() << endl;
}
