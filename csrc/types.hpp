#ifndef TYPES_HPP_
#define TYPES_HPP_


#include <iostream>
#include <string>
#include <map>
#include "enums.hpp"


using namespace std;

class Type {
  protected :
    TypeEnum type;
  public :
    Type(TypeEnum type) : type(type) {}
    bool isType(TypeEnum);
    string getType(void); // TODO rename this. imply a string
    virtual string _string(void)=0;
    virtual Type* flip(void)=0;
    void print(void);
};

class IntType : public Type {
  uint n;
  Dir dir;
  public :
    IntType(uint n, Dir dir) : Type(INT), n(n), dir(dir) {}
    uint numBits(void);
    string _string(void); 
    Type* flip(void);
};

class ArrayType : public Type {
  Type* baseType;
  uint len;
  public :
    ArrayType(Type *baseType, uint len) : Type(ARRAY), baseType(baseType), len(len) {}
    string _string(void);
    Type* flip(void);
    Type* idx();
};

class RecordType : public Type {
  map<string,Type*> record;
  public :
    RecordType(map<string,Type*> record) : Type(RECORD), record(record) {}
    string _string(void);
    Type* flip(void);
    Type* sel(string a);
    map<string,Type*> get(void);
};


//TODO This should be done in a better way
string Dir2Str(Dir d);
string TypeEnum2Str(TypeEnum t);

//UintType* Uint(uint bits, Dir dir);
IntType* Int(uint bits, Dir dir);
//FloatType* Float(uint ebits, uint mbits, Dir dir);
//BoolType* Bool(Dir dir);
ArrayType* Array(Type* baseType, uint len);
RecordType* Record(map<string,Type*> record);
RecordType* AddField(RecordType* record, string key, Type* val);
Type* Sel(Type* record, string key);
Type* Flip(Type*);

#endif //TYPES_HPP_
