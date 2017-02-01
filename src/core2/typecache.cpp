#ifndef TYPECACHE_CPP_
#define TYPECACHE_CPP_

#include "typecache.hpp"
using namespace std;

TypeCache::~TypeCache() {
  map<RecordTypeParams,RecordType*>::iterator it1;
  for (it1=RecordTypeCache.begin(); it1!=RecordTypeCache.end(); ++it1) {
    delete it1->second;
  }
  map<ArrayTypeParams,ArrayType*>::iterator it2;
  for (it2=ArrayTypeCache.begin(); it2!=ArrayTypeCache.end(); ++it2) {
    delete it2->second;
  }
  map<IntTypeParams,IntType*>::iterator it3;
  for (it3=IntTypeCache.begin(); it3!=IntTypeCache.end(); ++it3) {
    delete it3->second;
  }
}

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

RecordType* TypeCache::newRecord(RecordTypeParams params) {
  map<RecordTypeParams,RecordType*>::iterator it = RecordTypeCache.find(params);
  if (it != RecordTypeCache.end()) {
    return it->second;
  } else {
    RecordType* newRecordType = new RecordType(params);
    RecordTypeCache.emplace(params,newRecordType);
    return newRecordType;
  }
}

#endif //TYPECACHE_CPP_
