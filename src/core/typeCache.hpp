#ifndef TYPECACHE_HPP_
#define TYPECACHE_HPP_

#include <map>
#include "enums.hpp"
#include "types.hpp"
using namespace std;
class Type;
class IntType;
class ArrayType;
class RecordType;


typedef std::pair<uint32_t,Dir> IntTypeParams ;
typedef std::pair<Type*,uint32_t> ArrayTypeParams ;
typedef std::map<string,Type*> RecordTypeParams ;

class TypeCache {
  map<IntTypeParams,IntType*> IntTypeCache;
  map<ArrayTypeParams,ArrayType*> ArrayTypeCache;
  map<RecordTypeParams,RecordType*> RecordTypeCache;
  public :
    TypeCache() {}
    ~TypeCache();
    IntType* newInt(uint32_t n, Dir dir);
    ArrayType* newArray(Type* base, uint32_t len);
    RecordType* newRecord(RecordTypeParams params);
};
#endif //TYPECACHE_HPP_
