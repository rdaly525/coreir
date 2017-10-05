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

  boolType = new BoolType(c);
  intType = new IntType(c);
  stringType = new StringType(c);
  coreIRType = new CoreIRType(c);

}

TypeCache::~TypeCache() {
  for (auto it : RecordCache) delete it.second;
  
  //TODO this is a little sketch because the first key is the thing you are deleting...
  for (auto tpair : ArrayCache) {
    for (auto ttpair : tpair.second) {
      delete ttpair.second;
    }
  }
  delete bitI;
  delete bitO;
}


ArrayType* TypeCache::getArray(uint len, Type* t) {
  if (ArrayCache.count(t) && ArrayCache[t].count(len)) {
    return ArrayCache[t][len];
  } 
  else {
    ArrayType* a = new ArrayType(c,t,len);
    ArrayType* af = new ArrayType(c,c->Flip(t),len);
    a->setFlipped(af);
    af->setFlipped(a);
    ArrayCache[t][len] = a;
    ArrayCache[c->Flip(t)][len] = af;
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
    RecordType* rf = new RecordType(c,paramsF);
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
