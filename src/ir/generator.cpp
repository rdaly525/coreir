#include "coreir/ir/generator.h"
#include "coreir/ir/globalvalue.h"
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

Generator::Generator(Namespace* ns,string name,TypeGen* typegen, Params genparams) : GlobalValue(GVK_Generator,ns,name), typegen(typegen), genparams(genparams) {
  //Verify that typegen params are a subset of genparams
  for (auto const &type_param : typegen->getParams()) {
    auto const &gen_param = genparams.find(type_param.first);
    ASSERT(gen_param != genparams.end(),"Param not found: " + type_param.first);

    ASSERT(gen_param->second == type_param.second,"Param type mismatch for: " + gen_param->first + " (" + gen_param->second->toString()+ " vs " + type_param.second->toString()+")");
  }
}

Generator::~Generator() {
  if (def) {
    delete def;
  }
  for (auto m : genCache) {
    delete m.second;
  }
}

//This is the tough one
Module* Generator::getModule(Values genargs) {
  mergeValues(genargs,defaultGenArgs);
  if (genCache.count(genargs)) {
    return genCache[genargs];
  }
  
  checkValuesAreParams(genargs,genparams,getRefName());
  ASSERT(typegen->hasType(genargs),"Cannot create generated module!");
  Type* type = typegen->getType(genargs);
  string modname = this->name;
  Module* m;
  if (modParamsGen) {
    auto pc = modParamsGen(getContext(),genargs);
    m = new Module(ns,modname,type,pc.first,this,genargs);
    m->addDefaultModArgs(pc.second);
  }
  else {
     m = new Module(ns,modname,type,Params(),this,genargs);
  }
  genCache[genargs] = m;
  
  //TODO I am not sure what the default behavior should be
  //for not having a def
  //Run the generator if it has the def
  //if (this->hasDef()) {
  //  ModuleDef* mdef = m->newModuleDef();
  //  def->createModuleDef(mdef,genargs); 
  //  m->setDef(mdef);
  //}
  return m;
}

Module* Generator::getModule(Values genargs, Type* type) {
  mergeValues(genargs,defaultGenArgs);
  if (genCache.count(genargs)) {
    return genCache[genargs];
  }
  
  checkValuesAreParams(genargs,genparams,getRefName());
  if (typegen->hasType(genargs)) {
    ASSERT(typegen->getType(genargs) == type,"Cannot create module with inconsistent types");
  }
  string modname = this->name;
  Module* m;
  if (modParamsGen) {
    auto pc = modParamsGen(getContext(),genargs);
    m = new Module(ns,modname,type,pc.first,this,genargs);
    m->addDefaultModArgs(pc.second);
  }
  else {
     m = new Module(ns,modname,type,Params(),this,genargs);
  }
  genCache[genargs] = m;
  
  //TODO I am not sure what the default behavior should be
  //for not having a def
  //Run the generator if it has the def
  //if (this->hasDef()) {
  //  ModuleDef* mdef = m->newModuleDef();
  //  def->createModuleDef(mdef,genargs); 
  //  m->setDef(mdef);
  //}
  return m;
}

void Generator::eraseModule(Values genargs) {
  ASSERT(genCache.count(genargs),"Module does not exist!");
  delete genCache[genargs];
  genCache.erase(genargs);
}


bool Generator::runAll() {
  bool ret = false;
  for (auto mpair : genCache) {
    ret |= mpair.second->runGenerator();
  }
  return ret;
}
std::map<std::string,Module*> Generator::getGeneratedModules() {
  std::map<std::string,Module*> ret; 
  for (auto mpair : genCache) {
    ret.emplace(mpair.second->getLongName(),mpair.second);  
  }
  return ret;
}


void Generator::setGeneratorDefFromFun(ModuleDefGenFun fun) {
  //bool err = false;
  //for (auto gpair : genCache) err |= gpair.second->hasDef();
  //ASSERT(!err,"Cannot set generator defention when generator already ran!");
  if (this->def) delete this->def;
  this->def = new GeneratorDefFromFun(this,fun);
  
}

void Generator::addDefaultGenArgs(Values defaultGenArgs) {
  //Check to make sure each arg is in the gen params
  for (auto argmap : defaultGenArgs) {
    ASSERT(genparams.count(argmap.first)>0,"Cannot set default Gen Arg. Param " + argmap.first + " Does not exist!");
    this->defaultGenArgs[argmap.first] = argmap.second;
  }
}

string Generator::toString() const {
  string ret = "Generator: " + name;
  ret = ret + "\n    Params: " + ::CoreIR::toString(genparams);
  ret = ret + "\n    TypeGen: TODO";// + typegen->toString();
  ret = ret + "\n    Def? " + (hasDef() ? "Yes" : "No");
  return ret;
}

void Generator::print(void) const {
  cout << toString() << endl;
}

}//CoreIR namespace
