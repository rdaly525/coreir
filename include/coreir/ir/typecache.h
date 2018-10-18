#ifndef COREIR_TYPECACHE_HPP_
#define COREIR_TYPECACHE_HPP_

#include "fwd_declare.h"

namespace CoreIR {

struct RecordParamsHasher {
  size_t operator()(const RecordParams& rp) const {
    size_t hash = 0;
    for (auto it : rp) {
      size_t h = 0;
      hash_combine(h,it.first);
      hash_combine(h,it.second);
      hash ^= h;
    }
    return hash;
  }
};


//This stores Types and VTypes
class TypeCache {
  Context* c;
  BitInType* bitI;
  BitType* bitO;
  BitInOutType* bitIO;
  std::unordered_map<Type*,std::unordered_map<int,ArrayType*>> ArrayCache;
  std::unordered_map<RecordParams,RecordType*,RecordParamsHasher> RecordCache;
  
  AnyType* anyType;
  BoolType* boolType;
  IntType* intType;
  std::unordered_map<int,BitVectorType*> bitVectorCache;
  StringType* stringType;
  CoreIRType* coreIRType;
  ModuleType* moduleType;
  JsonType* jsonType;

  public :
    TypeCache(Context* c); 
    ~TypeCache();
    
    //Types
    BitType* getBit() { return bitO; }
    BitInType* getBitIn() { return bitI; }
    BitInOutType* getBitInOut() { return bitIO; }
    ArrayType* getArray(uint32_t len, Type* t);
    RecordType* getRecord(RecordParams params);

    //ValueTypes
    AnyType* getAny() { return anyType;}
    BoolType* getBool() { return boolType;}
    IntType* getInt() { return intType;}
    BitVectorType* getBitVector(int width);
    StringType* getString() { return stringType;}
    CoreIRType* getCoreIRType() { return coreIRType;}
    ModuleType* getModuleType() { return moduleType;}
    JsonType* getJsonType() { return jsonType;}

};

}//CoreIR namespace


#endif //TYPECACHE_HPP_
