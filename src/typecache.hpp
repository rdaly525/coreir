#ifndef TYPECACHE_HPP_
#define TYPECACHE_HPP_

#include <unordered_map>
#include "types.hpp"
#include "common.hpp"
#include "context.hpp"

using namespace std;

namespace CoreIR {

//RecordParams defined in types.hpp
//typedef std::pair<TypeGen*,Args*> TypeParams;

struct TypeParams {
  TypeGen* tg;
  Args args;
  TypeParams(TypeGen* tg, Args args) : tg(tg), args(args) {}
  friend bool operator==(const TypeParams & l,const TypeParams & r);
};



struct TypeParamsHasher {
  size_t operator()(const TypeParams& tgp) const;
};

struct TypeParamsEqFn {
  bool operator() (const TypeParams& l, const TypeParams& r) const;
}


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
  unordered_map<TypeParams,Type*,TypeParamsHasher> TypeGenCache;
  
  public :
    TypeCache(Context* c); 
    ~TypeCache();
    Type* newAny() { return any; }
    Type* newBitIn() { return bitI; }
    Type* newBitOut() { return bitO; }
    Type* newArray(uint32_t len, Type* t);
    Type* newRecord(RecordParams params);
    Type* newTypeGenInst(TypeGen* tgd, Args* args);
};

}//CoreIR namespace


#endif //TYPECACHE_HPP_
