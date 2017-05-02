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
  public :
    enum TypeKind {
      TK_Bit, TK_BitIn,TK_Array,TK_Record,TK_Named,TK_Any
    };
  protected :
    TypeKind kind;
    Type* flipped;
  public :
    Type(TypeKind kind) : kind(kind) {}
    virtual ~Type() {}
    TypeKind getKind() const {return kind;}
    
    void setFlipped(Type* f) { flipped = f;}
    Type* getFlipped() { return flipped;}
    virtual string toString(void) const =0;
    virtual bool sel(Context* c,string sel, Type** ret, Error* e);
    virtual bool hasInput() { return false;}
    virtual json toJson();
    void print(void);
    static string TypeKind2Str(TypeKind t);
};

std::ostream& operator<<(ostream& os, const Type& t);

class AnyType : public Type {
  public :
    AnyType() : Type(TK_Any) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Any;}
    string toString(void) const {return "Any";}
    
    bool sel(Context* c, string sel, Type** ret, Error* e);
};

class BitType : public Type {
  public :
    BitType() : Type(TK_Bit) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Bit;}
    string toString(void) const {return "Bit";}
};

class BitInType : public Type {
  public :
    BitInType() : Type(TK_BitIn) {}
    static bool classof(const Type* t) {return t->getKind()==TK_BitIn;}
    
    string toString(void) const {return "BitIn";}
    bool hasInput() { return true;}
};

class NamedType : public Type {
  protected :
    Namespace* ns;
    string name;
    
    Type* raw;

    bool isgen;
    TypeGen* typegen;
    Args genargs;
  public :
    NamedType(Namespace* ns, string name, Type* raw) : Type(TK_Named), ns(ns), name(name), raw(raw), isgen(false), typegen(nullptr) {}
    NamedType(Namespace* ns, string name, TypeGen* typegen, Args genargs);
    static bool classof(const Type* t) {return t->getKind()==TK_Named;}
    string toString(void) const { return name; } //TODO add generator
    string getName() {return name;}
    Type* getRaw() {return raw;}
    bool isGen() { return isgen;}
    TypeGen* getTypegen() { return typegen;}
    Args getGenargs() {return genargs;}
    
    json toJson();
    bool sel(Context* c, string sel, Type** ret, Error* e);

};

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Type *elemType, uint len) : Type(TK_Array), elemType(elemType), len(len) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Array;}
    uint getLen() {return len;}
    Type* getElemType() { return elemType; }
    string toString(void) const { 
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
    RecordType(RecordParams _record) : Type(TK_Record) {
      for(auto field : _record) {
        if(isNumber(field.first)) {
          cout << "Cannot have number as record field" << endl;
          exit(0);
        }
        record.emplace(field.first,field.second);
        _order.push_back(field.first);
      }
    }
    RecordType() : Type(TK_Record) {}
    void addItem(string s, Type* t) {
      _order.push_back(s);
      record.emplace(s,t);
    }
    static bool classof(const Type* t) {return t->getKind()==TK_Record;}
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
