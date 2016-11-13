#ifndef TYPECACHE_CPP_
#define TYPECACHE_CPP_

#include "typeCache.hpp"


IntType* TypeCache::newInt(uint32_t n, Dir dir) {
  IntTypeParams params(n,dir);
  map<IntTypeParams,IntType*>::iterator it = IntTypeCache.find(params);
  if (it != IntTypeCache.end()) {
    return it->second;
  } else {
    IntType* newIntType = new IntType(n,dir);
    IntTypeCache.emplace(params,newIntType);
    return newIntType;
  }
}

ArrayType* TypeCache::newArray(Type* base, uint32_t len) {
  ArrayTypeParams params(base,len);
  map<ArrayTypeParams,ArrayType*>::iterator it = ArrayTypeCache.find(params);
  if (it != ArrayTypeCache.end()) {
    return it->second;
  } else {
    ArrayType* newArrayType = new ArrayType(base,len);
    ArrayTypeCache.emplace(params,newArrayType);
    return newArrayType;
  }
}


#endif //TYPECACHE_CPP_
