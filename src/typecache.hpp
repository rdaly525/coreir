#ifndef TYPECACHE_HPP_
#define TYPECACHE_HPP_

#include <map>
#include "types.hpp"
#include "enums.hpp"
#include "context.hpp"

using namespace std;

typedef std::pair<uint,Type*> ArrayParams ;
//RecordParams defined in types.hpp
//typedef std::pair<TypeGen*,GenArgs*> TypeGenParams;

//TODO this could actually be super slow
// TODO this is not actually working

struct TypeGenParams {
  TypeGen* tgd;
  GenArgs* ga;
  TypeGenParams(TypeGen* tgd, GenArgs* ga) : tgd(tgd), ga(ga) {}
  friend bool operator==(TypeGenParams & l,TypeGenParams & r);
  friend bool operator!=(TypeGenParams & l,TypeGenParams & r);
  friend bool operator<(TypeGenParams a, TypeGenParams b);
};

class CoreIRContext;
class TypeCache {
  CoreIRContext* c;
  Type* bitI;
  Type* bitO;
  Type* any;
  map<ArrayParams,Type*> ArrayCache;
  map<RecordParams,Type*> RecordCache;
  map<TypeGenParams,Type*> TypeGenCache;
  //TODO TypeGenCache
  public :
    TypeCache(CoreIRContext* c); 
    ~TypeCache();
    Type* newAny() { return any; }
    Type* newBitIn() { return bitI; }
    Type* newBitOut() { return bitO; }
    Type* newArray(uint32_t len, Type* t);
    Type* newRecord(RecordParams params);
    Type* newTypeGenInst(TypeGen* tgd, GenArgs* args);
};
#endif //TYPECACHE_HPP_
