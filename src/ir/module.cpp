#include "coreir/ir/module.h"
#include "coreir/ir/generator.h"
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

Module::Module(Namespace* ns,std::string name, Type* type,Params modparams) : GlobalValue(GVK_Module,ns,name), Args(modparams), modparams(modparams), longname(name) {
  ASSERT(isa<RecordType>(type), "Module type needs to be a record!\n"+type->toString());
  this->type = cast<RecordType>(type);
}
Module::Module(Namespace* ns,std::string name, Type* type,Params modparams, Generator* g, Values genargs) : GlobalValue(GVK_Module,ns,name), Args(modparams), modparams(modparams), g(g), genargs(genargs) {
  ASSERT(isa<RecordType>(type), "Module type needs to be a record!\n"+type->toString());
  this->type = cast<RecordType>(type);
  ASSERT(g && genargs.size(),"Missing genargs!");
  this->longname = name + getContext()->getUnique(); //TODO do a better name
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

void Module::addDefaultModArgs(Values defaultModArgs) {
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
  return "Module: " + name + (isGenerated() ? ::CoreIR::toString(genargs) : "") + "\n  Type: " + type->toString() + "\n  Def? " + (hasDef() ? "Yes" : "No");
}

bool Module::runGenerator() {
  ASSERT(g,"Cannot Run Generator of module that is not gen!");
  if (!g->hasDef()) return false;
  if (this->hasDef()) return false;
  
  ModuleDef* mdef = this->newModuleDef();
  g->getDef()->createModuleDef(mdef,genargs); 
  this->setDef(mdef);
  return true;
}

void Module::print(void) const {
  cout << toString() << endl;
  if(def) def->print();

}

}//CoreIR namespace
