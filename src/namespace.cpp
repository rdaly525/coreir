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
  for(auto m : moduleList) delete m.second;
  for(auto g : generatorList) delete g.second;
  for(auto n : namedCache) delete n.second;
}

void Namespace::newNamedType(string name, string nameFlip, Type* raw) {
  //Make sure the name and its flip are different
  assert(name != nameFlip);
  //Verify this name and the flipped name do not exist yet
  assert(!typeGenList.count(name) && !typeGenList.count(nameFlip));
  NamedCacheParams ncp(name,Args());
  NamedCacheParams ncpFlip(nameFlip,Args());
  assert(!namedCache.count(ncp) && !namedCache.count(ncpFlip) );
  
  //Create two new NamedTypes
  NamedType* named = new NamedType(this,name,raw,TypeGen(),Args());
  NamedType* namedFlip = new NamedType(this,nameFlip,raw->getFlipped(),TypeGen(),Args());
  named->setFlipped(namedFlip);
  namedFlip->setFlipped(named);
  namedCache.emplace(ncp,named);
  namedCache.emplace(ncpFlip,namedFlip);
}

void Namespace::newNamedType(string name, string nameFlip, TypeGen typegen) {
  //Make sure the name and its flip are different
  assert(name != nameFlip);
  //Verify this name and the flipped name do not exist yet
  assert(!typeGenList.count(name) && !typeGenList.count(nameFlip));
  
  //Create flipped typegen
  TypeGen typegenFlip(typegen.params,typegen.fun,!typegen.flipped);
  
  //Add typegens into list
  typeGenList[name] = {typegen,nameFlip};
  typeGenList[nameFlip] = {typegenFlip,name};
}

//This has to be found. Error if not found
NamedType* Namespace::getNamedType(string name) {
  NamedCacheParams ncp(name,Args());
  auto found = namedCache.find(ncp);
  assert(found != namedCache.end());
  return found->second;
}

//Make sure the name is found in the typeGenCache. Error otherwise
//Then create a new entry in NamedCache if it does not exist
NamedType* Namespace::getNamedType(string name, Args genargs) {
  NamedCacheParams ncp(name,genargs);
  auto namedFound = namedCache.find(ncp);
  if (namedFound != namedCache.end() ) {
    return namedFound->second;
  }
  
  //Not found. Verify that name exists in TypeGenList
  auto tgenFound = typeGenList.find(name);
  assert(tgenFound != typeGenList.end());
  TypeGen tgen = tgenFound->second.first;
  string nameFlip = tgenFound->second.second;
  assert(typeGenList.count(nameFlip)>0);
  TypeGen tgenFlip = typeGenList.find(nameFlip)->second.first;
  NamedCacheParams ncpFlip(nameFlip,genargs);

  //TODO for now just run the generator.
  Type* raw = tgen.fun(this->c,genargs);
  if (tgen.flipped) {
    raw = raw->getFlipped();
  }

  //Create two new named entries
  NamedType* named = new NamedType(this,name,raw,tgen,genargs);
  NamedType* namedFlip = new NamedType(this,nameFlip,raw->getFlipped(),tgenFlip,genargs);
  named->setFlipped(namedFlip);
  namedFlip->setFlipped(named);
  namedCache[ncp] = named;
  namedCache[ncpFlip] = namedFlip;

  return named;
}

TypeGen Namespace::getTypeGen(string name) {
  auto found = typeGenList.find(name);
  assert(found != typeGenList.end());
  return found->second.first;
}



Generator* Namespace::newGeneratorDecl(string name, Params kinds, TypeGen tg) {
  Generator* g = new Generator(this,name,kinds,tg);
  generatorList.emplace(name,g);
  return g;
}

Module* Namespace::newModuleDecl(string name, Type* t, Params configparams) {
  Module* m = new Module(this,name,t, configparams);
  moduleList.emplace(name,m);
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
