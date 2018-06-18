#ifndef COREIR_VALUECACHE_HPP_
#define COREIR_VALUECACHE_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class BitVectorComp {
  public:
    bool operator() (const BitVector& l, const BitVector& r) const;
};

//class JsonComp {
//  public:
//    bool operator() (const Json& l, const Json& r) const;
//};

//This stores Values (Constants)
class ValueCache {
  Context* c;
  ConstBool* boolTrue;
  ConstBool* boolFalse;
  std::map<int,ConstInt*> intCache;
  std::map<BitVector,ConstBitVector*,BitVectorComp> bvCache;
  std::map<std::string,ConstString*> stringCache;
  std::map<Type*,ConstCoreIRType*> typeCache;
  std::map<Module*,ConstModule*> moduleCache;
  std::map<Json,ConstJson*> JsonCache;
  
  public :
    ValueCache(Context* c); 
    ~ValueCache();

    ConstBool* getBool(bool val);
    ConstInt* getInt(int val);
    ConstBitVector* getBitVector(BitVector val);
    ConstString* getString(std::string val);
    ConstCoreIRType* getType(Type* val);
    ConstModule* getModule(Module* val);
    ConstJson* getJson(Json val);

};

}//CoreIR namespace


#endif //TYPECACHE_HPP_
