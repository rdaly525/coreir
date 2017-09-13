#ifndef COREIR_TYPECACHE_HPP_
#define COREIR_TYPECACHE_HPP_

#include "fwd_declare.h"

namespace CoreIR {

struct RecordParamsHasher {
  size_t operator()(const RecordParams& rp) const {
    size_t hash = 0;
    for (auto it : rp) {
      hash_combine(hash,it);
    }
    return hash;
  }
};

class TypeCache {
  Context* c;
  Type* bitI;
  Type* bitO;
  Type* any;
  std::unordered_map<ArrayParams,Type*> ArrayCache; //Hasher is just the hash<myPair> definied in common
  std::unordered_map<RecordParams,Type*,RecordParamsHasher> RecordCache;
  
  public :
    TypeCache(Context* c); 
    ~TypeCache();
    Type* newAny() { return any; }
    Type* newBit() { return bitO; }
    Type* newBitIn() { return bitI; }
    Type* newArray(uint32_t len, Type* t);
    Type* newRecord(RecordParams params);
};

}//CoreIR namespace


#endif //TYPECACHE_HPP_
