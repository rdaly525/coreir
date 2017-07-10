#include <cassert>
#include <vector>
#include <set>

#include "instantiable.hpp"
#include "typegen.hpp"

using namespace std;

namespace CoreIR {

///////////////////////////////////////////////////////////
//-------------------- Instantiable ---------------------//
///////////////////////////////////////////////////////////
Context* Instantiable::getContext() { return ns->getContext();}

void Instantiable::setDefaultConfigArgs(Args defaultConfigArgs) {
  //Check to make sure each arg is in the config params
  for (auto argmap : defaultConfigArgs) {
    ASSERT(configparams.count(argmap.first)>0,"Arg " + argmap.first + " Does not exist!")
  }
  this->defaultConfigArgs = defaultConfigArgs;
}


bool operator==(const Instantiable & l,const Instantiable & r) {
  return l.isKind(r.getKind()) && (l.getName()==r.getName()) && (l.getNamespace()->getName() == r.getNamespace()->getName());
}

ostream& operator<<(ostream& os, const Instantiable& i) {
  os << i.toString();
  return os;
}

Generator::Generator(Namespace* ns,string name,TypeGen* typegen, Params genparams, Params configparams) : Instantiable(IK_Generator,ns,name,configparams), typegen(typegen), genparams(genparams) {
  //Verify that typegen params are a subset of genparams
  for (auto const &type_param : typegen->getParams()) {
    auto const &gen_param = genparams.find(type_param.first);
    ASSERT(gen_param != genparams.end(),"Param not found: " + type_param.first);
    ASSERT(gen_param->second == type_param.second,"Param type mismatch for " + type_param.first);
  }
}

Generator::~Generator() {
  if (def) {
    delete def;
  }
  //Delete all the Generated Modules only if they are Generated and not Namespace
  for (auto m : genCache) {
    if (m.second->getLinkageKind()==Instantiable::LK_Generated) { 
      delete m.second;
    }
  }
}


Module* Generator::getModule(Args args) {
  
  auto cached = genCache.find(args);
  if (cached != genCache.end() ) {
    return cached->second;
  }
  
  checkArgsAreParams(args,genparams);
  Type* type = typegen->getType(args);
  Module* m = new Module(ns,name + getContext()->getUnique(),type,configparams);
  m->setLinkageKind(Instantiable::LK_Generated);
  genCache[args] = m;
  return m;
}

//TODO maybe cache the results of this?
void Generator::setModuleDef(Module* m, Args args) {
  assert(def && "Cannot add ModuleDef if there is no generatorDef!");

  checkArgsAreParams(args,genparams);
  ModuleDef* mdef = m->newModuleDef();
  def->createModuleDef(mdef,this->getContext(),m->getType(),args); 
  m->setDef(mdef);
}

void Generator::setGeneratorDefFromFun(ModuleDefGenFun fun) {
  assert(!def && "Do you want to overwrite the def?");
  this->def = new GeneratorDefFromFun(this,fun);
}

void Generator::setDefaultGenArgs(Args defaultGenArgs) {
  //Check to make sure each arg is in the config params
  for (auto argmap : defaultGenArgs) {
    ASSERT(genparams.count(argmap.first)>0,"Arg " + argmap.first + " Does not exist!")
  }
  this->defaultGenArgs = defaultGenArgs;
}

string Generator::toString() const {
  string ret = "Generator: " + name;
  ret = ret + "\n    Params: " + Params2Str(genparams);
  ret = ret + "\n    TypeGen: TODO";// + typegen->toString();
  ret = ret + "\n    Def? " + (hasDef() ? "Yes" : "No");
  return ret;
}

DirectedModule* Module::newDirectedModule() {
  if (!directedModule) {
    directedModule = new DirectedModule(this);
  }
  return directedModule;
}

Module::~Module() {
  
  for (auto md : mdefList) delete md;
  delete directedModule;
}

ModuleDef* Module::newModuleDef() {
  
  ModuleDef* md = new ModuleDef(this);
  mdefList.push_back(md);
  return md;
}

bool Module::isEqual(Module* m0, Module* m1, bool checkConfig, bool checkInstNames,bool checkModuleNames) {
  //Check for the same configparams
  if (checkConfig && (m0->getConfigParams() != m1->getConfigParams())) {
    return false;
  }

  //Check if it is of the same type
  if (m0->getType() != m1->getType()) {
    return false;
  }
  
  //workqueue
  //while workqueue not done:
  //  instance,instance= pop
  //  get all wireables, wireables pairs.
  //  place all the connected instances in queue (if not in done set)
  //  remove first element of select paths for each pair.
  //  add to a map from SelectPath to SelectPath (for both pairs)
  //  check equality of the maps. 
  //  or something like that
  //check if all instances have:
  //  same type
  //  same genargs
  //  same configargs


  //for now as an approximate thing, just check that number of instances and number of connections are the same
  uint m0InstSize = m0->getDef()->getInstances().size();
  uint m1InstSize = m1->getDef()->getInstances().size();
  if (m0InstSize != m1InstSize) {
    return false;
  }

  uint m0ConSize = m0->getDef()->getConnections().size();
  uint m1ConSize = m1->getDef()->getConnections().size();
  if (m0ConSize != m1ConSize) {
    return false;
  }
  return true;

}

void Module::setDef(ModuleDef* def, bool validate) {
  if (validate) {
    if (def->validate()) {
      cout << "Error Validating def" << endl;
      this->getContext()->die();
    }
  }
  this->def = def;
  //Directed View is not valid anymore
  if (this->directedModule) {
    delete this->directedModule;
  }
}

string Module::toString() const {
  return "Module: " + name + "\n  Type: " + type->toString() + "\n  Def? " + (hasDef() ? "Yes" : "No");
}

void Module::print(void) {
  cout << toString() << endl;
  if(def) def->print();

}

}//CoreIR namespace
