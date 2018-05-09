#include "coreir/ir/namespace.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/common.h"
#include "coreir/ir/context.h"
#include "coreir/ir/types.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/module.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/error.h"

using namespace std;

namespace CoreIR {
Namespace::Namespace(Context* c, std::string name) : c(c), name(name) {
  checkStringSyntax(name);
}
Namespace::~Namespace() {
  for (auto m : moduleList) delete m.second;
  for (auto g : generatorList) delete g.second;
  for (auto n : namedTypeList) delete n.second;
  for (auto tg : typeGenList) delete tg.second;
}

//This will return all modules including all the generated ones
std::map<std::string,Module*> Namespace::getModules(bool includeGenerated) { 
  std::map<std::string,Module*> ret = moduleList;
  if (includeGenerated) {
    for (auto g : generatorList) {
      for (auto m : g.second->getGeneratedModules()) {
        ret.emplace(m);
      }
    }
  }
  return ret;
}

NamedType* Namespace::newNamedType(string name, string nameFlip, Type* raw) {
  //Make sure the name and its flip are different
  assert(name != nameFlip);
  //Verify this name and the flipped name do not exist yet
  assert(!typeGenList.count(name) && !typeGenList.count(nameFlip));
  assert(!namedTypeList.count(name) && !namedTypeList.count(nameFlip) );
  
  //Add name to namedTypeNameMap
  //namedTypeNameMap[name] = nameFlip;

  //Create two new NamedTypes
  NamedType* named = new NamedType(this,name,raw);
  NamedType* namedFlip = new NamedType(this,nameFlip,raw->getFlipped());
  named->setFlipped(namedFlip);
  namedFlip->setFlipped(named);
  namedTypeList[name] = named;
  namedTypeList[nameFlip] = namedFlip;
  return named;
}

bool Namespace::hasNamedType(string name) {
  return namedTypeList.count(name) > 0;
}

//This has to be found. Error if not found
NamedType* Namespace::getNamedType(string name) {
  auto found = namedTypeList.find(name);
  ASSERT(found != namedTypeList.end(),"Cannot find " + name);
  return found->second;
}


void Namespace::addTypeGen(TypeGen* typegen) {
  ASSERT(typegen->getNamespace() == this, "Adding typegen to a namespace different than its own");
  ASSERT(namedTypeList.count(typegen->getName())==0, "Name collision in addTypeGen");

  typeGenList[typegen->getName()] = typegen;
}

TypeGen* Namespace::newTypeGen(string name, Params genparams, TypeGenFun fun) {
  return TypeGenFromFun::make(this,name,genparams,fun);
}

TypeGen* Namespace::getTypeGen(string name) {
  ASSERT(typeGenList.count(name)>0, "missing typegen: " + name);
  TypeGen* ret = typeGenList.at(name);
  return ret;
}


Generator* Namespace::newGeneratorDecl(string name,TypeGen* typegen, Params genparams) {
  //Make sure module does not already exist as a module or generator
  ASSERT(moduleList.count(name)==0,"Already added " + name);
  ASSERT(generatorList.count(name)==0,"Already added " + name);
  
  Generator* g = new Generator(this,name,typegen,genparams);
  generatorList.emplace(name,g);
  return g;
}

Module* Namespace::newModuleDecl(string name, Type* t, Params configparams) {
  //Make sure module does not already exist as a module or generator
  ASSERT(moduleList.count(name)==0, name + " already exists in " + this->name);
  ASSERT(generatorList.count(name)==0, name + " already exists in " + this->name);
  ASSERT(isa<RecordType>(t),"Module type needs to be a record but is: " + t->toString());
  Module* m = new Module(this,name,t, configparams);
  moduleList[name] = m;
  return m;
}

void Namespace::eraseGenerator(std::string name) {
  ASSERT(generatorList.count(name),"Cannot delete generator because it does not exist! " + getName() + "." + name);
  delete generatorList[name];
  generatorList.erase(name);
}

void Namespace::eraseModule(std::string name) {
  //TODO hacky fix
  if (generatorList.count(name)) return;


  ASSERT(moduleList.count(name),"Cannot delete module because it does not exist!" + getName() + "." + name);
  delete moduleList[name];
  moduleList.erase(name);
}





Generator* Namespace::getGenerator(string gname) {
  auto it = generatorList.find(gname);
  if (it != generatorList.end()) return it->second;
  Error e;
  e.message("Could not find Generator in namespace!");
  e.message("  Generator: " + gname);
  e.message("  Namespace: " + name);
  e.fatal();
  c->error(e);
  return nullptr;
}
Module* Namespace::getModule(string mname) {
  auto it = moduleList.find(mname);
  if (it != moduleList.end()) return it->second;
  Error e;
  e.message("Could not find Module in namespace!");
  e.message("  Module: " + mname);
  e.message("  Namespace: " + name);
  e.fatal();
  c->error(e);
  return nullptr;
}

GlobalValue* Namespace::getGlobalValue(string iname) {
  if (moduleList.count(iname) > 0) return moduleList.at(iname);
  if (generatorList.count(iname) > 0) return generatorList.at(iname);
  Error e;
  e.message("Could not find GlobalValue in library!");
  e.message("  GlobalValue: " + iname);
  e.message("  Namespace: " + name);
  e.fatal();
  c->error(e);
  return nullptr;
}

void Namespace::print() {
  cout << "Namespace: " << name << endl;
  cout << "  Generators:" << endl;
  for (auto it : generatorList) it.second->print();
  for (auto it : moduleList) it.second->print();
  cout << endl;
}

}//CoreIR namespace
