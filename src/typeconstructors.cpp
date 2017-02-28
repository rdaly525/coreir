#ifndef TYPECONSTRUCTORS_CPP_
#define TYPECONSTRUCTORS_CPP_

#include "coreir.hpp"
#include "typecache.hpp"


//Global cache
// Should this be stored in the ModuleDef itself?
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
  if(!record->isKind(RECORD)) {
    cout << "ERROR: Can only Sel on a record\n";
    cout << "  Type: " << record << "\n";
  }
  return ((RecordType*)record)->sel(key);
}

Type* Flip(Type* type) {
  return type->flip(&typecache);
}

Type* In(Type* type) {
  return Flip(type);
}


//TODO might be int or Uint (add case for int8_t ...)
void* allocateFromType(Type* t) {
  void* d;
  //cout << "Trying to Allocating something for type " << *t << endl;
  if (t->isBase()) {
    //cout << "Allocating something\n";
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
  else if (t->isKind(ARRAY)) {
    ArrayType* a = (ArrayType*)t;
    d = (void**) malloc(a->getLen()*sizeof(void*));
    void** d_array = (void**) d;
    for(uint i=0; i<a->getLen(); ++i) {
      d_array[i] = allocateFromType(a->getElemType());
    }
  }
  else if (t->isKind(RECORD)) {
    RecordType* r = (RecordType*)t;
    vector<string> order = r->getOrder();
    d = (void**) malloc(order.size()*sizeof(void*));
    void** d_array = (void**) d;
    uint i=0;
    for(auto it=order.begin(); it!=order.end(); ++it, ++i) {
      d_array[i] = allocateFromType(r->sel(*it));
    }
  }
  else {
    throw "FUCK";
    exit(0);
  }
  return d;
}

void deallocateFromType(Type* t, void* d) {
  if (t->isBase()) {
    free(d);
  }
  else if (t->isKind(ARRAY)) {
    ArrayType* a = (ArrayType*)t;
    void** d_array = (void**) d;
    for(uint i=0; i<a->getLen(); ++i) {
      deallocateFromType(a->getElemType(),d_array[i]);
    }
    free(d_array);
  }
  else if (t->isKind(RECORD)) {
    RecordType* r = (RecordType*)t;
    vector<string> order = r->getOrder();
    void** d_array = (void**) d;
    uint i=0;
    for(auto it=order.begin(); it!=order.end(); ++it, ++i) {
      deallocateFromType(r->sel(*it),d_array[i]);
    }
    free(d_array);
  }
  else {
    throw "FUCK";
    exit(0);
  }

}




#endif //TYPECONSTRUCTORS_CPP_
