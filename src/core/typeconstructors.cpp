#ifndef TYPECONSTRUCTORS_CPP_
#define TYPECONSTRUCTORS_CPP_

#include "coreir.hpp"
#include "typeCache.hpp"


//Global cache
// Should this be stored in the Module itself?
TypeCache typecache;


IntType* Int(uint bits, Dir dir) {
  return typecache.newInt(bits,dir);
}
IntType* Int(uint bits) {
  return typecache.newInt(bits,OUT);
}
//FloatType* Float(uint ebits, uint mbits, Dir dir);
//BoolType* Bool(Dir dir);
ArrayType* Array(Type* elemType, uint len) {
  return typecache.newArray(elemType,len);
}
RecordType* Record(vector<std::pair<string,Type*>> record) {
  return typecache.newRecord(record);
}

Type* Sel(Type* record, string key) {
  if(!record->isType(RECORD)) {
    cout << "ERROR: Can only Sel on a record\n";
    cout << "  Type: " << record << "\n";
  }
  return ((RecordType*)record)->sel(key);
}
Type* Flip(Type* type) {
  return type->flip(&typecache);
}

void* allocateFromType(Type* t) {
  void* d;
  if (t->isBase()) {
    uint n = ((BaseType*)t)->numBits();
    if (n <= 8) d = (uint8_t*) malloc(sizeof(uint8_t));
    else if (n <= 16) d = (uint16_t*) malloc(sizeof(uint16_t));
    else if (n <= 32) d = (uint32_t*) malloc(sizeof(uint32_t));
    else if (n <= 64) d = (uint64_t*) malloc(sizeof(uint64_t));
    else {
      exit(0);
      throw "FUCK";
    }
  }
  else {
    d = NULL;
    //TODO
  }
  return d;
}

void deallocateFromType(Type* t, void* v) {

}




#endif //TYPECONSTRUCTORS_CPP_
