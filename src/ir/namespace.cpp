#include "coreir/ir/namespace.h"
#include "coreir/ir/casting/casting.h"
#include "coreir/ir/common.h"
#include "coreir/ir/context.h"
#include "coreir/ir/types.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/instantiable.h"
#include "coreir/ir/error.h"

using namespace std;

namespace CoreIR {

Namespace::~Namespace() {
  for (auto m : moduleList) delete m.second;
  for (auto g : generatorList) delete g.second;
  for (auto n : namedTypeList) delete n.second;
  for (auto nmap : namedTypeGenCache) {
    for (auto n : nmap.second) {
      delete n.second;
    }
  }
  for (auto tg : typeGenList) delete tg.second;
}

//This will return all modules including all the generated ones
//TODO 
std::map<std::string,Module*> Namespace::getModules() { 
  std::map<std::string,Module*> ret = moduleList;
  for (auto g : generatorList) {
    for (auto m : g.second->getModules()) {
      ret.emplace(m);
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
  namedTypeNameMap[name] = nameFlip;

  //Create two new NamedTypes
  NamedType* named = new NamedType(this,name,raw);
  NamedType* namedFlip = new NamedType(this,nameFlip,raw->getFlipped());
  named->setFlipped(namedFlip);
  namedFlip->setFlipped(named);
  namedTypeList[name] = named;
  namedTypeList[nameFlip] = namedFlip;
  return named;
}

//TODO
void Namespace::newNominalTypeGen(string name, string nameFlip, Params genparams, TypeGenFun fun) {
  //Make sure the name and its flip are different
  assert(name != nameFlip);
  //Verify this name and the flipped name do not exist yet
  assert(!typeGenList.count(name) && !typeGenList.count(nameFlip));
  assert(!namedTypeList.count(name) && !namedTypeList.count(nameFlip) );
 
  //Add name to typeGenNameMap
  typeGenNameMap[name] = nameFlip;
  typeGenNameMap[nameFlip] = name;

  //Create the TypeGens
  TypeGen* typegen = new TypeGenFromFun(this,name,genparams,fun,false);
  TypeGen* typegenFlip = new TypeGenFromFun(this,nameFlip,genparams,fun,true);
  
  //Add typegens into list
  typeGenList[name] = typegen;
  typeGenList[nameFlip] = typegenFlip;
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

//Check if cached in namedTypeGenCache
//Make sure the name is found in the typeGenCache. Error otherwise
//Then create a new entry in NamedCache if it does not exist
NamedType* Namespace::getNamedType(string name, Values genargs) {
  ASSERT(typeGenList.count(name),this->name + "." + name + " was never defined");
  assert(typeGenNameMap.count(name));

  if (namedTypeGenCache[name].count(genargs)) {
    return namedTypeGenCache[name][genargs];
  }
  //Not found in cache. Create the entry
  //Not found. Verify that name exists in TypeGenList
  TypeGen* tgen = typeGenList[name];
  assert(typeGenNameMap.count(name));
  string nameFlip = typeGenNameMap.at(name);
  assert(typeGenList.count(nameFlip));
  TypeGen* tgenFlip = typeGenList.at(nameFlip);

  //Create two new named entries
  NamedType* named = new NamedType(this,name,tgen,genargs);
  NamedType* namedFlip = new NamedType(this,nameFlip,tgenFlip,genargs);
  named->setFlipped(namedFlip);
  namedFlip->setFlipped(named);
  namedTypeGenCache[name][genargs] = named;
  namedTypeGenCache[nameFlip][genargs] = namedFlip;
  ASSERT(namedTypeGenCache.count(name),"Bad name missing");
  ASSERT(namedTypeGenCache[name].count(genargs),"Bad args missing");

  return named;
}
TypeGen* Namespace::newTypeGen(string name, Params genparams, TypeGenFun fun) {
  assert(namedTypeList.count(name)==0);
  assert(typeGenList.count(name)==0);
  
  TypeGen* typegen = new TypeGenFromFun(this,name,genparams,fun);
  
  //Add name to typeGenNameMap
  typeGenNameMap[name] = "";
  
  typeGenList[name] = typegen;
  return typegen;
}

//TODO deal with at errors
TypeGen* Namespace::getTypeGen(string name) {
  ASSERT(typeGenList.count(name)>0, "missing typegen: " + name);
  TypeGen* ret = typeGenList.at(name);
  assert(ret->getName()==name);
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

Instantiable* Namespace::getInstantiable(string iname) {
  if (moduleList.count(iname) > 0) return moduleList.at(iname);
  if (generatorList.count(iname) > 0) return generatorList.at(iname);
  Error e;
  e.message("Could not find Instantiable in library!");
  e.message("  Instantiable: " + iname);
  e.message("  Namespace: " + name);
  e.fatal();
  c->error(e);
  return nullptr;
}

//TODO Update this
void Namespace::print() {
  cout << "Namespace: " << name << endl;
  cout << "  Generators:" << endl;
  for (auto it : generatorList) it.second->print();
  for (auto it : moduleList) it.second->print();
  cout << endl;
}

}//CoreIR namespace
