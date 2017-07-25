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

class NamedType;
class Type {
  public :
    enum TypeKind {TK_Bit=0, TK_BitIn=1,TK_Array=2,TK_Record=3,TK_Named=4,TK_Any=5};
    enum DirKind {DK_In,DK_Out,DK_Mixed,DK_Unknown};
  protected :
    TypeKind kind;

    //Mixed means mixed of in and out, Unknown means unknown
    DirKind dir;
    
    Context* c;
    Type* flipped;
  public :
    Type(TypeKind kind,DirKind dir, Context* c) : kind(kind), dir(dir), c(c) {}
    virtual ~Type() {}
    TypeKind getKind() const {return kind;}
    DirKind getDir() const {return dir;}
    void setFlipped(Type* f) { flipped = f;}
    Type* getFlipped() { return flipped;}
    virtual string toString(void) const =0;
    virtual bool sel(string sel, Type** ret, Error* e);
    virtual uint getSize() const=0;
    virtual json toJson();
    void print(void);
    static string TypeKind2Str(TypeKind t);
    
    //"sugar" for making arrays
    Type* Arr(uint i);
    
    bool isInput() const { return dir==DK_In;}
    bool isOutput() const { return dir==DK_Out; }
    bool isMixed() const { return dir==DK_Mixed; }
    bool isUnknown() const { return dir==DK_Unknown; }
    bool hasInput() const { return isInput() || isMixed(); }

};

std::ostream& operator<<(ostream& os, const Type& t);

class AnyType : public Type {
  public :
    AnyType(Context* c) : Type(TK_Any,DK_Unknown,c) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Any;}
    string toString(void) const {return "Any";}
    
    bool sel(string sel, Type** ret, Error* e);
    uint getSize() const { return 0;}
};

class BitType : public Type {
  public :
    BitType(Context* c) : Type(TK_Bit,DK_Out,c) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Bit;}
    string toString(void) const {return "Bit";}
    uint getSize() const { return 1;}
};

class BitInType : public Type {
  public :
    BitInType(Context* c) : Type(TK_BitIn,DK_In,c) {}
    static bool classof(const Type* t) {return t->getKind()==TK_BitIn;}
    
    string toString(void) const {return "BitIn";}
    uint getSize() const { return 1;}
};

class NamedType : public Type {
  protected :
    Namespace* ns;
    string name;
    
    Type* raw;

    bool isgen=false;
    TypeGen* typegen=nullptr;
    Args genargs;
  public :
    NamedType(Context* c, Namespace* ns, string name, Type* raw) : Type(TK_Named,raw->getDir(),c), ns(ns), name(name), raw(raw) {}
    NamedType(Context* c, Namespace* ns, string name, TypeGen* typegen, Args genargs);
    static bool classof(const Type* t) {return t->getKind()==TK_Named;}
    string toString(void) const { return name; } //TODO add generator
    string getName() {return name;}
    Type* getRaw() {return raw;}
    bool isGen() { return isgen;}
    TypeGen* getTypegen() { return typegen;}
    Args getGenArgs() {return genargs;}
    uint getSize() const { return raw->getSize();}
    
    json toJson();
    bool sel(string sel, Type** ret, Error* e);
};

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Context* c,Type *elemType, uint len) : Type(TK_Array,elemType->getDir(),c), elemType(elemType), len(len) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Array;}
    uint getLen() {return len;}
    Type* getElemType() { return elemType; }
    string toString(void) const { 
      return elemType->toString() + "[" + to_string(len) + "]";
    };
    json toJson();
    bool sel(string sel, Type** ret, Error* e);
    uint getSize() const { return len * elemType->getSize();}

};


class RecordType : public Type {
  unordered_map<string,Type*> record;
  vector<string> _order;
  public :
    RecordType(Context* c, RecordParams _record);
    RecordType(Context* c) : Type(TK_Record,DK_Unknown,c) {}
    void addItem(string s, Type* t);
    static bool classof(const Type* t) {return t->getKind()==TK_Record;}
    vector<string> getOrder() { return _order;}
    unordered_map<string,Type*> getRecord() { return record;}
    string toString(void) const;
    json toJson();
    bool sel(string sel, Type** ret, Error* e);
    uint getSize() const;
};

}//CoreIR namespace


#endif //TYPES_HPP_
