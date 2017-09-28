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


//This stores Types and VTypes
class TypeCache {
  Context* c;
  BitInType* bitI;
  BitType* bitO;
  std::unordered_map<ArrayParams,Type*> ArrayCache; //Hasher is just the hash<myPair> definied in common
  std::unordered_map<RecordParams,Type*,RecordParamsHasher> RecordCache;
  
  BoolType* boolType;
  IntType* intType;
  std::unordered_map<int,BitVectorType*> BitVectorCache;
  StringType* stringType;
  CoreIRType* coreIRType;

  public :
    TypeCache(Context* c); 
    ~TypeCache();
    
    //Types
    BitType* getBit() { return bitO; }
    BitInType* getBitIn() { return bitI; }
    ArrayType* getArray(uint32_t len, Type* t);
    RecordType* getRecord(RecordParams params);

    //ValueTypes
    BoolType* getBool() { return boolType;}
    IntType* getInt() { return intType;}
    BitVectorType* getBitVector(int width);
    StringType* getString() { return stringType;}
    CoreIRType* getCoreIRType() { return coreIRType;}

};

}//CoreIR namespace


#endif //TYPECACHE_HPP_
