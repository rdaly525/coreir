#ifndef TYPECACHE_HPP_
#define TYPECACHE_HPP_

#include <unordered_map>
#include "types.hpp"
#include "common.hpp"
#include "context.hpp"

using namespace std;

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

//struct ArrayParamsHasher {
//  size_t operator()(const ArrayParams& rp) const {
//     
//  }
//};

class Context;
class TypeCache {
  Context* c;
  Type* bitI;
  Type* bitO;
  Type* any;
  unordered_map<ArrayParams,Type*> ArrayCache; //Hasher is just the hash<myPair> definied in common
  unordered_map<RecordParams,Type*,RecordParamsHasher> RecordCache;
  
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
