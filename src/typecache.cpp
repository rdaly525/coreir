#ifndef TYPECACHE_CPP_
#define TYPECACHE_CPP_

#include "typecache.hpp"
#include <cassert>

using namespace std;
bool operator==(TypeGenParams & l,TypeGenParams & r) {
  return (l.tgd==r.tgd) && (*l.ga == *r.ga);
}
bool operator!=(TypeGenParams & l,TypeGenParams & r) { return !(l == r); }
bool operator<(TypeGenParams a, TypeGenParams b) {
  if (a.tgd != b.tgd) return a.tgd < b.tgd;
  return *(a.ga) < *(b.ga);
}

TypeCache::TypeCache(CoreIRContext* c) : c(c) {
  bitI = new BitInType();
  bitO = new BitOutType();
  bitI->setFlipped(bitO);
  bitO->setFlipped(bitI);
  any = new AnyType();
  any->setFlipped(any);
}

TypeCache::~TypeCache() {
  for (auto it1 : RecordCache) {
    delete it1.second;
  }
  for (auto it2 : ArrayCache) {
    delete it2.second;
  }
  delete bitI;
  delete bitO;
  delete any;
}


Type* TypeCache::newArray(uint len, Type* t) {
  ArrayParams params(len,t);
  auto it = ArrayCache.find(params);
  if (it != ArrayCache.end()) {
    return it->second;
  } 
  else {
    Type* a = new ArrayType(t,len);
    Type* af = new ArrayType(c->Flip(t),len);
    a->setFlipped(af);
    af->setFlipped(a);
    ArrayCache.emplace(params,a);
    ArrayParams paramsF(len,c->Flip(t));
    ArrayCache.emplace(paramsF,af);
    return a;
  }
}

Type* TypeCache::newRecord(RecordParams params) {
  auto it = RecordCache.find(params);
  if (it != RecordCache.end()) {
    return it->second;
  } 
  else {
    Type* r = new RecordType(params);
    
    // Create params for flipped
    RecordParams paramsF;
    for (auto p : params) {
      paramsF.push_back({p.first,c->Flip(p.second)});
    }
    Type* rf = new RecordType(paramsF);
    r->setFlipped(rf);
    rf->setFlipped(r);

    RecordCache.emplace(params,r);
    RecordCache.emplace(paramsF,rf);
    return r;
  }
}

Type* TypeCache::newTypeGenInst(TypeGen* tgd, GenArgs* args) {
  TypeGenParams params(tgd,args);
  auto it = TypeGenCache.find(params);
  if (it != TypeGenCache.end()) {
    return it->second;
  }
  else {
    Type* t = new TypeGenType(tgd,args);
    Type* tf = new TypeGenType(tgd->flipped,args);
    t->setFlipped(tf);
    tf->setFlipped(t);
    TypeGenCache.emplace(params,t);
    TypeGenParams paramsF(tgd->flipped,args);
    TypeGenCache.emplace(paramsF,tf);
    return t;
  }
}


#endif //TYPECACHE_CPP_
