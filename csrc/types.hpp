#ifndef TYPES_HPP_
#define TYPES_HPP_


#include <iostream>
#include <string>
#include <map>
#include "enums.hpp"


using namespace std;

class Type {
  TypeEnum name;
  public :
    Type(TypeEnum name) : name(name) {}
    string getType(void);
    virtual string _string(void)=0;
    void print(void);
};

class IntType : public Type {
  uint32_t n;
  Dir dir;
  public :
    IntType(uint32_t n, Dir dir) : Type(INT), n(n), dir(dir) {}
    uint32_t numBits(void);
    string _string(void); 
};

class ArrayType : public Type {
  Type* baseType;
  uint32_t len;
  public :
    ArrayType(Type *baseType, uint32_t len) : Type(ARRAY), baseType(baseType), len(len) {}
    string _string(void);
};

class RecordType : public Type {
  map<string,Type*> record;
  public :
    RecordType(map<string,Type*> record) : Type(RECORD), record(record) {}
    string _string(void);
    Type* operator[](string sel);
};


//TODO This should be done in a better way
string Dir2Str(Dir d);
string TypeEnum2Str(TypeEnum t);

//UintType* Uint(uint bits, Dir dir);
IntType* Int(uint bits, Dir dir);
//FloatType* Float(uint ebits, uint mbits, Dir dir);
//BoolType* Bool(Dir dir);
ArrayType* Array(Type* baseType, uint len);
//RecordType* Record(string key, Type* val,...);
//RecordType* AddField(RecordType* record, string key, Type* val);

//Type* Select(RecordType* iface, string key);
//Type* Flip(Type* type);




#endif //TYPES_HPP_
