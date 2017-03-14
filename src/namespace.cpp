#ifndef NAMESPACE_CPP_
#define NAMESPACE_CPP_


#include "namespace.hpp"

using namespace std;

bool operator==(const GenCacheParams & l,const GenCacheParams & r) {
  return (*l.g==*r.g) && (*l.ga==*r.ga);
}

bool operator!=(const GenCacheParams & l,const GenCacheParams & r) {
  return !(l==r);
}

size_t GenCacheParamsHasher::operator()(const GenCacheParams& gcp) const {
  size_t hash = 0;
  hash_combine(hash,gcp.g->getNamespace()->getName());
  hash_combine(hash,gcp.g->getName());
  hash_combine(hash,*gcp.ga);
  return hash;
}
  
Namespace::~Namespace() {
  for(auto m : mList) delete m.second;
  for(auto g : gList) delete g.second;
  for(auto t : tList) delete t.second;

  // Delete genCache;
  //for(auto g : genCache) delete g.second;
}

TypeGen* Namespace::newTypeGen(string name, string nameFlipped, GenParams kinds, TypeGenFun fun) {
      assert(!hasTypeGen(name));
      assert(!hasTypeGen(nameFlipped));
      TypeGen* t = new TypeGen(name,name,kinds,fun,false);
      TypeGen* tf = new TypeGen(name,nameFlipped,kinds,fun,true);
      t->setFlipped(tf);
      tf->setFlipped(t);
      tList.emplace(name,t);
      tList.emplace(nameFlipped,tf);
      return t;
    }

//TODO deal with name conflicts
//bool Context::registerLib(Namespace* lib) {
//  string name = lib->getName();
//  if (libs.find(name) != libs.end()) {
//    Error e;
//    e.message("Namespace already exists!");
//    e.message("  Namespace: " + name);
//    error(e);
//    return true;
//  }
//  libs.emplace(name,lib);
//  return false;
//}

Generator* Namespace::newGeneratorDecl(string name, GenParams kinds, TypeGen* tg) {
  Generator* g = new Generator(this,name,kinds,tg);
  gList.emplace(name,g);
  return g;
}

Module* Namespace::newModuleDecl(string name, Type* t, GenParams configparams) {
  for (auto it : configparams) cout << "P: " << it.first << GenParam2Str(it.second) << endl;
  Module* m = new Module(this,name,t, configparams);
  mList.emplace(name,m);
  return m;
}

Generator* Namespace::getGenerator(string gname) {
  auto it = gList.find(gname);
  if (it != gList.end()) return it->second;
  Error e;
  e.message("Could not find Generator in namespace!");
  e.message("  Generator: " + gname);
  e.message("  Namespace: " + name);
  e.fatal();
  c->error(e);
  return nullptr;
}
Module* Namespace::getModule(string mname) {
  auto it = mList.find(mname);
  if (it != mList.end()) return it->second;
  Error e;
  e.message("Could not find Module in namespace!");
  e.message("  Module: " + mname);
  e.message("  Namespace: " + name);
  e.fatal();
  c->error(e);
  return nullptr;
}

Instantiable* Namespace::getInstantiable(string iname) {
  if (mList.count(iname) > 0) return mList.at(iname);
  if (gList.count(iname) > 0) return gList.at(iname);
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
  for (auto it : gList) cout << "    " << it.second->toString() << endl;
  cout << endl;
}

Module* Namespace::runGenerator(Generator* g, GenArgs* ga) {
  GenCacheParams gcp(g,ga);
  auto it = genCache.find(gcp);
  if (it != genCache.end()) return it->second;
  cout << "Did not find in cache. Actualy running generator" << endl;
  TypeGen* tg = g->getTypeGen();
  
  //Run the typegen first
  Type* type = tg->fun(c,ga,tg->genparams);
  
  //Run the generator
  Module* mNew= g->getDef()(c,type,ga,tg->genparams);
  genCache.emplace(gcp,mNew);
  return mNew;
}


#endif // NAMESPACE_CPP_
