#ifndef NAMESPACE_CPP_
#define NAMESPACE_CPP_


#include "namespace.hpp"

using namespace std;

namespace CoreIR {

bool operator==(const GenCacheParams & l,const GenCacheParams & r) {
  return (*l.g==*r.g) && (l.ga==r.ga);
}

size_t GenCacheParamsHasher::operator()(const GenCacheParams& gcp) const {
  size_t hash = 0;
  hash_combine(hash,gcp.g->getNamespace()->getName());
  hash_combine(hash,gcp.g->getName());
  return hash;
}

bool operator==(const NamedCacheParams& l,const NamedCacheParams& r) {
  return (l.name==r.name) && (l.args==r.args);
}

size_t NamedCacheParamsHasher::operator()(const NamedCacheParams& ncp) const {
  size_t hash = 0;
  hash_combine(hash,ncp.name);
  hash_combine(hash,ncp.args);
  return hash;
}
  
Namespace::~Namespace() {
  for (auto m : moduleList) delete m.second;
  for (auto g : generatorList) delete g.second;
  for (auto n : namedTypeList) delete n.second;
  for (auto n : namedTypeGenCache) delete n.second;
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
  NamedType* named = new NamedType(this,name,raw,TypeGen(),Args());
  NamedType* namedFlip = new NamedType(this,nameFlip,raw->getFlipped(),TypeGen(),Args());
  named->setFlipped(namedFlip);
  namedFlip->setFlipped(named);
  namedTypeList[name] = named;
  namedTypeList[nameFlip] = namedFlip;
  return named;
}

void Namespace::newNominalTypeGen(string name, string nameFlip, Params genparams, TypeGenFun fun) {
  //Make sure the name and its flip are different
  assert(name != nameFlip);
  //Verify this name and the flipped name do not exist yet
  assert(!typeGenList.count(name) && !typeGenList.count(nameFlip));
  assert(!namedTypeList.count(name) && !namedTypeList.count(nameFlip) );
 
  //Add name to typeGenNameMap
  typeGenNameMap[name] = nameFlip;

  //Create the TypeGens
  TypeGen typegen(this,name,genparams,fun,false);
  TypeGen typegenFlip(this,nameFlip,genparams,fun,true);
  
  //Add typegens into list
  typeGenList[name] = typegen;
  typeGenList[nameFlip] = typegenFlip;
}

//TODO does not tell me which kind
bool Namespace::hasNamedType(string name) {
  return typeGenNameMap.count(name) > 0 || namedTypeNameMap.count(name) > 0;
}

//This has to be found. Error if not found
NamedType* Namespace::getNamedType(string name) {
  auto found = namedTypeList.find(name);
  assert(found != namedTypeList.end());
  return found->second;
}

//Check if cached in namedTypeGenCache
//Make sure the name is found in the typeGenCache. Error otherwise
//Then create a new entry in NamedCache if it does not exist
NamedType* Namespace::getNamedType(string name, Args genargs) {
  NamedCacheParams ncp(name,genargs);
  auto namedFound = namedTypeGenCache.find(ncp);
  if (namedFound != namedTypeGenCache.end() ) {
    return namedFound->second;
  }
  
  //Not found. Verify that name exists in TypeGenList
  //TODO deal with the 'at' error possiblities
  TypeGen tgen = typeGenList.at(name);
  string nameFlip = typeGenNameMap.at(name);
  TypeGen tgenFlip = typeGenList.at(nameFlip);
  NamedCacheParams ncpFlip(nameFlip,genargs);

  //TODO for now just run the generator.
  Type* raw = tgen.run(this->c,genargs);

  //Create two new named entries
  NamedType* named = new NamedType(this,name,raw,tgen,genargs);
  NamedType* namedFlip = new NamedType(this,nameFlip,raw->getFlipped(),tgenFlip,genargs);
  named->setFlipped(namedFlip);
  namedFlip->setFlipped(named);
  namedTypeGenCache[ncp] = named;
  namedTypeGenCache[ncpFlip] = namedFlip;

  return named;
}
void Namespace::newTypeGen(string name, Params genparams, TypeGenFun fun) {
  assert(namedTypeList.count(name)==0);
  assert(typeGenList.count(name)==0);
  
  TypeGen typegen(this,name,genparams,fun);
  
  //Add name to typeGenNameMap
  typeGenNameMap[name] = "";
  
  typeGenList[name] = typegen;
}

//TODO deal with at errors
TypeGen Namespace::getTypeGen(string name) {
  TypeGen ret = typeGenList.at(name);
  assert(ret.name==name);
  return ret;
}



Generator* Namespace::newGeneratorDecl(string name, Params genparams, TypeGen typegen) {
  //Make sure module does not already exist as a module or generator
  assert(moduleList.count(name)==0);
  assert(generatorList.count(name)==0);
  
  Generator* g = new Generator(this,name,genparams,typegen);
  generatorList.emplace(name,g);
  return g;
}

Module* Namespace::newModuleDecl(string name, Type* t, Params configparams) {
  //Make sure module does not already exist as a module or generator
  assert(moduleList.count(name)==0);
  assert(generatorList.count(name)==0);

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
  e.message("Could not find Instance in library!");
  e.message("  Instance: " + iname);
  e.message("  Namespace: " + name);
  e.fatal();
  c->error(e);
  return nullptr;
}

//TODO Update this
void Namespace::print() {
  cout << "Namespace: " << name << endl;
  cout << "  Generators:" << endl;
  for (auto it : generatorList) cout << "    " << it.second->toString() << endl;
  cout << endl;
}

Module* Namespace::runGenerator(Generator* g, Args genargs, Type* t) {
  GenCacheParams gcp(g,genargs);
  auto it = genCache.find(gcp);
  if (it != genCache.end()) return it->second;
  cout << "Did not find in cache. Actualy running generator" << endl;
  
  // Make new module TODO how to pass configs
  string mNewName = "TODO" + to_string(rand());
  Module* mNew = this->newModuleDecl(mNewName,t);
  if (g->getDef()) {
    ModuleDef* mdef = mNew->newModuleDef();
    g->getDef()(mdef,c,t,genargs);
    mNew->addDef(mdef);
  }
  genCache.emplace(gcp,mNew);
  return mNew;
}

}//CoreIR namespace


#endif // NAMESPACE_CPP_
