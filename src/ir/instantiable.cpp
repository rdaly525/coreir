#include "coreir/ir/instantiable.h"
#include "coreir/ir/common.h"
#include "coreir/ir/context.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/types.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/generatordef.h"
#include "coreir/ir/directedview.h"
#include "coreir/ir/valuetype.h"
#include "coreir/ir/value.h"

using namespace std;

namespace CoreIR {

///////////////////////////////////////////////////////////
//-------------------- Instantiable ---------------------//
///////////////////////////////////////////////////////////

//bool operator==(const Instantiable & l,const Instantiable & r) {
//  return l.isKind(r.getKind()) && (l.getName()==r.getName()) && (l.getNamespace()->getName() == r.getNamespace()->getName());
//}

ostream& operator<<(ostream& os, const Instantiable& i) {
  os << i.toString();
  return os;
}

Generator::Generator(Namespace* ns,string name,TypeGen* typegen, Params genparams) : Instantiable(IK_Generator,ns,name), typegen(typegen), genparams(genparams) {
  //Verify that typegen params are a subset of genparams
  for (auto const &type_param : typegen->getParams()) {
    auto const &gen_param = genparams.find(type_param.first);
    ASSERT(gen_param != genparams.end(),"Param not found: " + type_param.first);
    ASSERT(gen_param->second == type_param.second,"Param type mismatch for " + type_param.first);
    ASSERT(gen_param->second == type_param.second,"Param type mismatch for: " + gen_param->first + " (" + gen_param->second->toString()+ " vs " + type_param.second->toString()+")");
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

//This is the tough one
Module* Generator::getModule(Consts genargs) {
  
  if (genCache.count(genargs)) {
    return genCache[genargs];
  }
  
  checkValuesAreParams(castMap<Value>(genargs),genparams);
  Type* type = typegen->getType(genargs);
  string modname;
  if (nameGen) {
    modname = nameGen(genargs);
  }
  else {
    modname = this->name + getContext()->getUnique(); //TODO
  }
  Module* m;
  if (modParamsGen) {
    std::pair<Params,Consts> pc = modParamsGen(getContext(),genargs);
    m = new Module(ns,modname,type,pc.first);
    m->addDefaultModArgs(pc.second);
  }
  else {
     m = new Module(ns,modname,type);
  }
  m->setLinkageKind(Instantiable::LK_Generated);
  genCache[genargs] = m;
  
  //TODO I am not sure what the default behavior should be
  //for not having a def
  //Run the generator if it has the def
  if (this->hasDef()) {
    ModuleDef* mdef = m->newModuleDef();
    def->createModuleDef(mdef,genargs); 
    m->setDef(mdef);
  }
  return m;
}

void Generator::setGeneratorDefFromFun(ModuleDefGenFun fun) {
  ASSERT(!def,"Do you really want to overwrite the def? No.");
  this->def = new GeneratorDefFromFun(this,fun);
}

void Generator::addDefaultGenArgs(Consts defaultGenArgs) {
  //Check to make sure each arg is in the gen params
  for (auto argmap : defaultGenArgs) {
    ASSERT(genparams.count(argmap.first)>0,"Cannot set default Gen Arg. Param " + argmap.first + " Does not exist!")
    this->defaultGenArgs[argmap.first] = argmap.second;
  }
}

string Generator::toString() const {
  string ret = "Generator: " + name;
  ret = ret + "\n    Params: " + Params2Str(genparams);
  ret = ret + "\n    TypeGen: TODO";// + typegen->toString();
  ret = ret + "\n    Def? " + (hasDef() ? "Yes" : "No");
  return ret;
}

void Generator::print(void) {
  cout << toString() << endl;
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

void Module::addDefaultModArgs(Consts defaultModArgs) {
  //Check to make sure each arg is in the mod params
  for (auto argmap : defaultModArgs) {
    ASSERT(modparams.count(argmap.first),"Cannot set default module arg. Param " + argmap.first + " Does not exist!")
    this->defaultModArgs[argmap.first] = argmap.second;
  }
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
