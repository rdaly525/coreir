#ifndef TYPECACHE_CPP_
#define TYPECACHE_CPP_

#include "typecache.hpp"
#include "args.hpp"

using namespace std;

namespace CoreIR {


bool TypeParamsEqFn::operator()(const TypeParams& l,const TypeParams& r) const {
  bool ret = (l.typegen==r.typegen);
  if(!ret) return false;
  return (l.genargs == r.genargs);
}

size_t TypeParamsHasher::operator()(const TypeParams& tgp) const {
    size_t hash = 0;
    hash_combine(hash,tgp.typegen);
    hash_combine(hash,tgp.genargs);
    return hash;
}

TypeCache::TypeCache(Context* c) : c(c) {
  bitI = new BitInType();
  bitO = new BitOutType();
  bitI->setFlipped(bitO);
  bitO->setFlipped(bitI);
  any = new AnyType();
  any->setFlipped(any);
}

TypeCache::~TypeCache() {
  for (auto it : RecordCache) delete it.second;
  for (auto it : ArrayCache) delete it.second;
  for (auto it : TypeGenCache) delete it.second;
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

Type* TypeCache::newTypeGenInst(TypeGen* tgd, Args args) {
  TypeParams params(tgd,args);
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
    TypeParams paramsF(tgd->flipped,args);
    TypeGenCache.emplace(paramsF,tf);
    return t;
  }
}

}//CoreIR namespace


#endif //TYPECACHE_CPP_
