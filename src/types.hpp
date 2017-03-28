#ifndef TYPES_HPP_
#define TYPES_HPP_


#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
#include <cassert>

#include "common.hpp"
#include "args.hpp"
#include "context.hpp"
#include "error.hpp"
#include "json.hpp"

using json = nlohmann::json;

using namespace std;

namespace CoreIR {

class Type {
  protected :
    TypeKind kind;
    Type* flipped;
  public :
    Type(TypeKind kind) : kind(kind) {}
    virtual ~Type() {}
    bool isKind(TypeKind k) {return k==kind;}
    TypeKind getKind() {return kind;}
    void setFlipped(Type* f) { flipped = f;}
    Type* getFlipped() { return flipped;}
    virtual string toString(void) const =0;
    virtual bool sel(Context* c,string sel, Type** ret, Error* e);
    virtual bool hasInput() { return false;}
    virtual json toJson();
    void print(void);
};

std::ostream& operator<<(ostream& os, const Type& t);

class AnyType : public Type {
  public :
    AnyType() : Type(ANY) {}
    string toString(void) const {return "Any";}
    bool sel(Context* c, string sel, Type** ret, Error* e);
};

class BitInType : public Type {
  public :
    BitInType() : Type(BITIN) {}
    string toString(void) const {return "BitIn";}
    bool hasInput() { return true;}
};

class BitOutType : public Type {
  public :
    BitOutType() : Type(BITOUT) {}
    string toString(void) const {return "BitOut";}
};

struct Named {
  Namespace* ns;
  string name;
  Type* raw;
  Named(Namespace* ns, string name, Type* raw) : ns(ns), name(name), raw(raw) {}
  void setFlipped(TypeGen* _flipped) {
    flipped = _flipped;
  }
};

struct NamedGen : Named {
  Params genparams;
  TypeGenFun fun;
  bool funflip;
  TypeGen(Namespace* ns, string name, Params genparams, TypeGenFun fun, bool funflip) : Named(ns,name), name(name), genparams(genparams), fun(fun), funflip(funflip) { 

  string toString() {
    return name + Params2Str(genparams);
  }

}

setNamedFlipped("clk","clkIn");

Type* clk = ns->getNamedType("clk");
Type* clk ns->new

NamedType
  Namespace
  string name
  Type* raw;

NamedGenType
  Namespace
  string name
  
  Params genparams
  function genfun
  bool flipped;

  Args genargs
  Type* raw;


// TODO check argtypes are actually the same as genparams
class NamedType : public Type {
  protected :
    Named* def;
    Type* raw;
    Args genargs;
  public :
    TypeGenType(TypeGen* def, Args genargs);
    TypeGen* getDef() { return def;}
    Args getArgs() { return genargs;}
    string toString(void) const { return def->name; }
    //json toJson(); TODO
    bool sel(Context* c, string sel, Type** ret, Error* e);

};

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Type *elemType, uint len) : Type(ARRAY), elemType(elemType), len(len) {}
    uint getLen() {return len;}
    Type* getElemType() { return elemType; }
    string toString(void) const { 
      //return TypeKind2Str(this->kind) + "<" + elemType->toString() + ">[" + to_string(len) + "]";
      return elemType->toString() + "[" + to_string(len) + "]";
    };
    json toJson();
    bool sel(Context* c, string sel, Type** ret, Error* e);
    bool hasInput() {return elemType->hasInput();}

};


class RecordType : public Type {
  unordered_map<string,Type*> record;
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
    unordered_map<string,Type*> getRecord() { return record;}
    string toString(void) const;
    json toJson();
    bool sel(Context* c, string sel, Type** ret, Error* e);
    bool hasInput() {
      for ( auto it : record ) {
        if (it.second->hasInput()) return true;
      }
      return false;
    }

};

}//CoreIR namespace


#endif //TYPES_HPP_
