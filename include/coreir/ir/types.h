#ifndef COREIR_TYPES_HPP_
#define COREIR_TYPES_HPP_

#include "fwd_declare.h"
#include "globalvalue.h"

namespace CoreIR {

class Type {
  public :
    enum TypeKind {TK_Bit=0, TK_BitIn=1,TK_Array=2,TK_Record=3,TK_Named=4, TK_BitInOut=5};
    enum DirKind {DK_In,DK_Out,DK_InOut,DK_Mixed,DK_Null};
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
    virtual std::string toString(void) const =0;
    Type* sel(std::string sel);
    std::vector<std::string> getSelects();
    bool canSel(std::string sel);
    bool canSel(SelectPath path);
    virtual uint getSize() const=0;
    virtual void print(void) const;
    Context* getContext() {return c; };
    static std::string TypeKind2Str(TypeKind t);
    
    //"sugar" for making arrays
    Type* Arr(uint i);
    //Getting the flipped version
    Type* getFlipped() { return flipped;}
    
    bool isInput() const { return dir==DK_In;}
    bool isOutput() const { return dir==DK_Out; }
    bool isInOut() const { return dir==DK_InOut; }
    bool isMixed() const { return dir==DK_Mixed; }
    bool isUnknown() const { return dir==DK_Null; }
    bool hasInput() const;

    bool isBaseType();

  private :
    friend class TypeCache;
    friend class Namespace;
    void setFlipped(Type* f) { flipped = f;}


};

std::ostream& operator<<(std::ostream& os, const Type& t);

class BitType : public Type {
  public :
    BitType(Context* c) : Type(TK_Bit,DK_Out,c) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Bit;}
    std::string toString(void) const override {return "Bit";}
    uint getSize() const override { return 1;}
};

class BitInType : public Type {
  public :
    BitInType(Context* c) : Type(TK_BitIn,DK_In,c) {}
    static bool classof(const Type* t) {return t->getKind()==TK_BitIn;}
    
    std::string toString(void) const override {return "BitIn";}
    uint getSize() const override { return 1;}
};

class BitInOutType : public Type {
  public :
    BitInOutType(Context* c) : Type(TK_BitInOut,DK_InOut,c) {}
    static bool classof(const Type* t) {return t->getKind()==TK_BitInOut;}
    
    std::string toString(void) const override {return "BitInOut";}
    uint getSize() const override { return 1;}
};

class NamedType : public Type, public GlobalValue {
  protected :
    
    Type* raw;

    bool isgen=false;
    TypeGen* typegen=nullptr;
    Values genargs;
  public :
    NamedType(Namespace* ns, std::string name, Type* raw);
    NamedType(Namespace* ns, std::string name, TypeGen* typegen, Values genargs);
    static bool classof(const Type* t) {return t->getKind()==TK_Named;}
    std::string toString(void) const override { return this->getRefName(); } //TODO add generator
    void print() const override;
    Type* getRaw() const {return raw;}
    bool isGen() const { return isgen;}
    TypeGen* getTypegen() const { return typegen;}
    Values getGenArgs() const {return genargs;}
    uint getSize() const override { return raw->getSize();}
};

class ArrayType : public Type {
  Type* elemType;
  uint len;
  public :
    ArrayType(Context* c,Type *elemType, uint len) : Type(TK_Array,elemType->getDir(),c), elemType(elemType), len(len) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Array;}
    uint getLen() const {return len;}
    Type* getElemType() const { return elemType; }
    std::string toString(void) const override { 
      return elemType->toString() + "[" + std::to_string(len) + "]";
    };
    uint getSize() const override { return len * elemType->getSize();}

};


class RecordType : public Type {
  std::map<std::string,Type*> record;
  std::vector<std::string> _order;
  public :
    RecordType(Context* c, RecordParams _record);
    RecordType(Context* c) : Type(TK_Record,DK_Null,c) {}
    static bool classof(const Type* t) {return t->getKind()==TK_Record;}
    const std::vector<std::string>& getFields() const { return _order;}
    const std::map<std::string,Type*>& getRecord() const { return record;}
    std::string toString(void) const override;
    uint getSize() const override;
    
    //nice functions for creating a new type with or without a field
    RecordType* appendField(std::string label, Type* t); 
    RecordType* detachField(std::string label);

};

}//CoreIR namespace


#endif //TYPES_HPP_
