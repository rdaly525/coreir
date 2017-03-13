#ifndef TYPECACHE_HPP_
#define TYPECACHE_HPP_

#include <unordered_map>
#include "types.hpp"
#include "common.hpp"
#include "context.hpp"

using namespace std;


//RecordParams defined in types.hpp
//typedef std::pair<TypeGen*,GenArgs*> TypeGenParams;

struct TypeGenParams {
  TypeGen* tg;
  GenArgs* ga;
  TypeGenParams(TypeGen* tg, GenArgs* ga) : tg(tg), ga(ga) {}
  friend bool operator==(const TypeGenParams & l,const TypeGenParams & r);
  friend bool operator!=(const TypeGenParams & l,const TypeGenParams & r);
};

struct TypeGenParamsHasher {
  size_t operator()(const TypeGenParams& tgp) const;
};

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
  unordered_map<TypeGenParams,Type*,TypeGenParamsHasher> TypeGenCache;
  
  public :
    TypeCache(Context* c); 
    ~TypeCache();
    Type* newAny() { return any; }
    Type* newBitIn() { return bitI; }
    Type* newBitOut() { return bitO; }
    Type* newArray(uint32_t len, Type* t);
    Type* newRecord(RecordParams params);
    Type* newTypeGenInst(TypeGen* tgd, GenArgs* args);
};
#endif //TYPECACHE_HPP_
