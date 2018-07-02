#ifndef COREIR_VALUE_TYPE_HPP_
#define COREIR_VALUE_TYPE_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class ValueType {
  public:
    enum ValueTypeKind {
      VTK_Bool=0,
      VTK_Int=1,
      VTK_BitVector=2,
      VTK_String=3,
      VTK_CoreIRType=4,
      VTK_Module=5,
      VTK_Json=6,
      VTK_Any=7,
    };
  private :
    ValueTypeKind kind;
    Context* c;
  public :
    ValueType(Context* c,ValueTypeKind kind) : kind(kind), c(c) {}
    ValueTypeKind getKind() const {return kind;}
    std::string toString();
    Context* getContext() {return c;}
};

class BoolType : public ValueType {
  public :
    BoolType(Context* c) : ValueType(c,VTK_Bool) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_Bool;}
    static BoolType* make(Context* c);
};

class IntType : public ValueType {
  public :
    IntType(Context* c) : ValueType(c,VTK_Int) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_Int;}
    static IntType* make(Context* c);
};

class BitVectorType : public ValueType {
  int width;
  public : 
    BitVectorType(Context* c,int width) : ValueType(c,VTK_BitVector), width(width) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_BitVector;}
    static BitVectorType* make(Context* c, int width=32);
    int getWidth() { return width;}
};

class StringType : public ValueType {
  public :
    StringType(Context* c) : ValueType(c,VTK_String) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_String;}
    static StringType* make(Context* c);
};

class CoreIRType : public ValueType {
  public : 
    CoreIRType(Context* c) : ValueType(c,VTK_CoreIRType) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_CoreIRType;}
    static CoreIRType* make(Context* c);
};

class ModuleType : public ValueType {
  public :
    ModuleType(Context* c) : ValueType(c,VTK_Module) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_Module;}
    static ModuleType* make(Context* c);
};

class JsonType : public ValueType {
  public :
    JsonType(Context* c) : ValueType(c,VTK_Json) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_Json;}
    static JsonType* make(Context* c);
};

class AnyType : public ValueType {
  public :
    AnyType(Context* c) : ValueType(c,VTK_Any) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_Any;}
    static AnyType* make(Context* c);
};


}
#endif
