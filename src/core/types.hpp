#ifndef TYPES_HPP_
#define TYPES_HPP_


#include <iostream>
#include <string>
#include <map>
#include <vector>
#include "enums.hpp"
#include "genargs.hpp"
#include <cassert>

using namespace std;

struct GenArgs;
class Type {
  protected :
    TypeKind kind;
    Type* flipped;
  public :
    Type(TypeKind kind) : kind(kind) {}
    virtual ~Type() {}
    bool isKind(TypeKind k) {return k==kind;}
    void setFlipped(Type* f) { flipped = f;}
    Type* getFlipped() { return flipped;}
    virtual string toString(void) const =0;
    void print(void);
};


std::ostream& operator<<(ostream& os, const Type& t);


class AnyType : public Type {
  public :
    AnyType() : Type(ANY) {}
    string toString(void) const {return "Any";}
};

class BitInType : public Type {
  public :
    BitInType() : Type(BITIN) {}
    string toString(void) const {return "BitIn";}
};

class BitOutType : public Type {
  public :
    BitOutType() : Type(BITOUT) {}
    string toString(void) const {return "BitOut";}
};

class Context;
typedef Type* (*TypeGenFun)(Context* c, GenArgs* args, ArgKinds kinds);
struct TypeGen {
  string libname;
  string name;
  TypeGen* flipped;
  ArgKinds kinds;
  TypeGenFun fun;
  bool funflip;
  TypeGen(string libname, string name, ArgKinds kinds, TypeGenFun fun, bool funflip) : libname(libname), name(name), kinds(kinds), fun(fun), funflip(funflip) {
  }
  void setFlipped(TypeGen* _flipped) {
    flipped = _flipped;
  }
};


// TODO check argtypes are actually the same as kinds
class TypeGenType : public Type {
  protected :
    TypeGen* def;
    GenArgs* args;
  public :
    TypeGenType(TypeGen* def, GenArgs* args);
    TypeGen* getDef() { return def;}
    GenArgs* getArgs() { return args;}
    string toString(void) const { return def->name; }
    //bool isEqual(Type* t);

};

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Type *elemType, uint len) : Type(ARRAY), elemType(elemType), len(len) {}
    uint getLen() {return len;}
    Type* getElemType() { return elemType; }
    string toString(void) const { 
      return TypeKind2Str(this->kind) + "<" + elemType->toString() + ">[" + to_string(len) + "]";
    };
};

typedef vector<std::pair<string,Type*>> RecordParams ;

class RecordType : public Type {
  map<string,Type*> record;
  vector<string> _order;
  public :
    RecordType(RecordParams _record) : Type(RECORD) {
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
};


#endif //TYPES_HPP_
