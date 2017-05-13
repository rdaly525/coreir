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

bool operator==(const Instantiable & l,const Instantiable & r) {
  return l.isKind(r.getKind()) && (l.getName()==r.getName()) && (l.getNamespace()->getName() == r.getNamespace()->getName());
}

ostream& operator<<(ostream& os, const Instantiable& i) {
  os << i.toString();
  return os;
}

Generator::Generator(Namespace* ns,string name,TypeGen* typegen, Params genparams, Params configparams) : Instantiable(IK_Generator,ns,name,configparams), typegen(typegen), genparams(genparams), def(nullptr) {
  //Verify that typegen params are a subset of genparams
  for (auto const &type_param : typegen->getParams()) {
    auto const &gen_param = genparams.find(type_param.first);
    assert(gen_param != genparams.end() && "Param not found");
    assert(gen_param->second == type_param.second && "Param type mismatch");
  }
}

Generator::~Generator() {
  if (def) {
    delete def;
  }
  //Delete all the Generated Modules
  for (auto m : genCache) delete m.second;
}

void checkArgsAreParams(Args args, Params params) {
  assert(args.size() == params.size() && "Args and params are not the same!");
  for (auto const &param : params) {
    auto const &arg = args.find(param.first);
    assert(arg != args.end() && "Arg Not found");
    assert(arg->second->getKind() == param.second && "Param type mismatch");
  }
}

Module* Generator::getModule(Args args) {
  //Check cache
  cout << "Getting from " << name << Args2Str(args) << endl;
  auto cached = genCache.find(args);
  if (cached != genCache.end() ) {
    return cached->second;
  }
  
  checkArgsAreParams(args,genparams);
  Type* type = typegen->getType(args);
  Module* m = new Module(ns,name + getContext()->getUnique(),type,configparams);
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

string Generator::toString() const {
  string ret = "Generator: " + name;
  ret = ret + "\n    Params: " + Params2Str(genparams);
  ret = ret + "\n    TypeGen: TODO";// + typegen->toString();
  ret = ret + "\n    Def? " + (hasDef() ? "Yes" : "No");
  return ret;
}

DirectedModule* Module::newDirectedModule() {
    DirectedModule* directed_module = new DirectedModule(this);
    directedModuleList.push_back(directed_module);
    return directed_module;
}

Module::~Module() {
  
  for (auto md : mdefList) delete md;
  for (auto directedModule : directedModuleList) delete directedModule;
}

string Module::toString() const {
  return "Module: " + name + "\n  Type: " + type->toString() + "\n  Def? " + (hasDef() ? "Yes" : "No");
}

void Module::print(void) {
  cout << toString() << endl;
  if(def) def->print();

}

}//CoreIR namespace
