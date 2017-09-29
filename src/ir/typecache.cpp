#include "coreir/ir/typecache.h"
#include "coreir/ir/context.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/types.h"
#include "coreir/ir/valuetype.h"

using namespace std;

namespace CoreIR {

TypeCache::TypeCache(Context* c) : c(c) {
  bitO = new BitType(c);
  bitI = new BitInType(c);
  bitI->setFlipped(bitO);
  bitO->setFlipped(bitI);
}

TypeCache::~TypeCache() {
  for (auto it : RecordCache) delete it.second;
  for (auto it : ArrayCache) delete it.second;
  delete bitI;
  delete bitO;
}


ArrayType* TypeCache::getArray(uint len, Type* t) {
  ArrayParams params(len,t);
  auto it = ArrayCache.find(params);
  if (it != ArrayCache.end()) {
    return it->second;
  } 
  else {
    ArrayType* a = new ArrayType(c,t,len);
    Type* af = new ArrayType(c,c->Flip(t),len);
    a->setFlipped(af);
    af->setFlipped(a);
    ArrayCache.emplace(params,a);
    ArrayParams paramsF(len,c->Flip(t));
    ArrayCache.emplace(paramsF,af);
    return a;
  }
}

RecordType* TypeCache::getRecord(RecordParams params) {
  auto it = RecordCache.find(params);
  if (it != RecordCache.end()) {
    return it->second;
  } 
  else {
    RecordType* r = new RecordType(c,params);
    
    // Create params for flipped
    RecordParams paramsF;
    for (auto p : params) {
      paramsF.push_back({p.first,c->Flip(p.second)});
    }
    Type* rf = new RecordType(c,paramsF);
    r->setFlipped(rf);
    rf->setFlipped(r);

    RecordCache.emplace(params,r);
    RecordCache.emplace(paramsF,rf);
    return r;
  }
}

BitVectorType* TypeCache::getBitVector(int width) {
  if (bitVectorCache.count(width)) return bitVectorCache[width];
  BitVectorType* bv = new BitVectorType(c,width);
  bitVectorCache.emplace(width,bv);
  return bv;
}

}//CoreIR namespace
