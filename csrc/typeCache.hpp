#ifndef TYPECACHE_HPP_
#define TYPECACHE_HPP_

#include <map>
#include "enums.hpp"
#include "types.hpp"
using namespace std;
class Type;
class IntType;
class ArrayType;

typedef std::pair<uint32_t,Dir> IntTypeParams ;
typedef std::pair<Type*,uint32_t> ArrayTypeParams ;

class TypeCache {
  map<IntTypeParams,IntType*> IntTypeCache;
  map<ArrayTypeParams,ArrayType*> ArrayTypeCache;
  public :
    TypeCache() {}
    IntType* newInt(uint32_t n, Dir dir);
    ArrayType* newArray(Type* base, uint32_t len);
};
#endif //TYPECACHE_HPP_
