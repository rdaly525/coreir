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
    TypeEnum type;
    bool _hasInput;
  public :
    Type(TypeEnum type, bool _hasInput) : type(type), _hasInput(_hasInput) {}
    virtual ~Type() {}
    bool isType(TypeEnum);
    bool isBase() {return !(isType(RECORD) || isType(ARRAY));}
    bool hasInput() { return _hasInput;};
    virtual string toString(void) const =0;
    virtual Type* flip(TypeCache*)=0;
    void print(void);
};

std::ostream& operator<<(ostream& os, const Type&);

class BaseType : public Type {
  protected :
    uint n;
    Dir dir;
  public :
    BaseType(TypeEnum type, uint n,Dir dir) : Type(type,dir==IN), n(n), dir(dir) {}
    uint numBits(void) {return n;}
    Dir getDir(void) {return dir;}
    virtual Type* flip(TypeCache*)=0;
};

class IntType : public BaseType {
  public :
    IntType(uint n, Dir dir) : BaseType(INT,n,dir) {}
    string toString(void) const; 
    Type* flip(TypeCache*);
    Dir getDir() { return dir; }
};

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Type *elemType, uint len) : Type(ARRAY,elemType->hasInput()), elemType(elemType), len(len) {}
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
    RecordType(recordparam_t _record) : Type(RECORD,false) {
      //TODO do not change this auto. some reason it does not work
      for(recordparam_t::iterator it=_record.begin(); it!=_record.end(); ++it) {
        if(isNumber(it->first)) {
          cout << "Cannot have number as record field" << endl;
          exit(0);
        }
        record.emplace(it->first,it->second);
        _order.push_back(it->first);
        _hasInput |= it->second->hasInput();
      }
    }
    RecordType() : Type(RECORD,false) {}
    void addItem(string s, Type* t) {
      _order.push_back(s);
      record.emplace(s,t);
    }
    vector<string> getOrder() { return _order;}
    string toString(void) const;
    Type* flip(TypeCache*);
    Type* sel(string a);
    map<string,Type*> getRecord() { return record;}
};


#endif //TYPES_HPP_
