#ifndef TYPES_HPP_
#define TYPES_HPP_


#include <iostream>
#include <string>
#include <map>
#include <vector>
#include "enums.hpp"
#include "typecache.hpp"


using namespace std;

class TypeCache;

class Type {
  protected :
    TypeKind kind;
  public :
    Type(TypeKind kind) : kind(kind) {}
    virtual ~Type() {}
    bool isKind(TypeKind);
    bool isBase() {return isKind(BIT) || isKind(TDEF);}
    virtual string toString(void) const =0;
    virtual Type* flip(TypeCache*)=0;
    void print(void);
};

std::ostream& operator<<(ostream& os, const Type&);

class BaseType : public Type {
  protected :
    Dir dir;
  public :
    BaseType(TypeKind kind, Dir dir) : Type(kind), dir(dir) {}
    Dir getDir(void) {return dir;}
    virtual Type* flip(TypeCache*)=0;
};

class BitType : public BaseType {
  public :
    BitType(Dir dir) : BaseType(BIT,dir) {}
    Type* flip(TypeCache*);
}

class TypeDef : public BaseType {
  protected :
    string name;
    Type* raw;
  public : 
    TypeDef(string name, Type* raw, Dir dir=Out) : BaseType(TDEF,dir), name(name), raw(raw) {}
}

typedef Type* (*typegenfun_t)(NameSpace*,GenArgs*);
class TypeGenDef : public Type {
  protected :
    string name;
    typegenfun_t genfun;
    GenArgs* genargs;
  public :
    TypeGenDef(string name, typegenfun_t genfun, GenArgs* genargs) : Type(TGDEF), name(name), genfun(genfun), genargs(genargs)
}

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Type *elemType, uint len) : Type(ARRAY), elemType(elemType), len(len) {}
    string toString(void) const;
    Type* flip(TypeCache*);
    Type* sel(uint);
    uint getLen() {return len;}
    Type* getElemType() { return elemType; }
};


typedef vector<std::pair<string,Type*>> recordparam_t;

class RecordType : public Type {
  map<string,Type*> record;
  vector<string> _order;
  public :
    RecordType(recordparam_t _record) : Type(RECORD) {
      //TODO do not change this auto. some reason it does not work
      for(auto field : _record) {
        if(isNumber(field.first)) {
          cout << "Cannot have number as record field" << endl;
          exit(0);
        }
        record.emplace(field.first,field.second);
        _order.push_back(field.first);
      }
    }
    RecordType() : Type(RECORD) {}
    void addItem(string s, Type* t) {
      _order.push_back(s);
      record.emplace(s,t);
    }
    vector<string> getOrder() { return _order;}
    map<string,Type*> getRecord() { return record;}
    string toString(void) const;
    Type* flip(TypeCache*);
    Type* sel(string a);
};


#endif //TYPES_HPP_
