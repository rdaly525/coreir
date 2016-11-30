#ifndef TYPES_HPP_
#define TYPES_HPP_


#include <iostream>
#include <string>
#include <map>
#include "enums.hpp"
#include "typeCache.hpp"


using namespace std;

class TypeCache;

class Type {
  protected :
    TypeEnum type;
    bool _hasInput;
  public :
    Type(TypeEnum type, bool _hasInput) : type(type), _hasInput(_hasInput) {}
    virtual ~Type() {}
    bool isType(TypeEnum);
    bool isBase() {return !(isType(RECORD) || isType(ARRAY));}
    bool hasInput() { return _hasInput;};
    string getType(void); // TODO rename this. imply a string
    virtual string _string(void)=0;
    virtual Type* flip(TypeCache*)=0;
    void print(void);
};

class BaseType : public Type {
  protected :
    Dir dir;
  public :
    BaseType(TypeEnum type, Dir dir) : Type(type,dir==IN), dir(dir) {}
    virtual Type* flip(TypeCache*)=0;
};

class IntType : public BaseType {
  uint n;
  public :
    IntType(uint n, Dir dir) : BaseType(INT,dir), n(n) {}
    uint numBits(void);
    string _string(void); 
    Type* flip(TypeCache*);
    Dir getDir() { return dir; }
};

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Type *elemType, uint len) : Type(ARRAY,elemType->hasInput()), elemType(elemType), len(len) {}
    string _string(void);
    Type* flip(TypeCache*);
    Type* idx(uint);
    uint getLen() {return len;}
    Type* getBaseType() { return baseType; }
};

class RecordType : public Type {
  map<string,Type*> record;
  public :
    RecordType(map<string,Type*> record);
    string _string(void);
    Type* flip(TypeCache*);
    Type* sel(string a);
    map<string,Type*> getRecord() { return record;}
};


#endif //TYPES_HPP_
