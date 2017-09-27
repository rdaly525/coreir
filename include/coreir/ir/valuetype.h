#ifndef COREIR_VALUE_TYPE_HPP_
#define COREIR_VALUE_TYPE_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class ValueType {
  public:
    enum ValueTypeKind {
      VTK_Bool=0,
      VTK_Int=1,
      VTK_String=2,
      VTK_CoreIRType=3,
    };
  private :
    ValueTypeKind kind;
    Context* c;
  public :
    ValueType(ValueTypeKind kind) : kind(kind) {}
    ValueTypeKind getKind() const {return kind;}
};

class BoolType : public ValueType {
  public
    BoolType() : ValueType(VTK_Bool) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_Bool;}
    static BoolType* make(Context* c) {return 
}

class IntType : public ValueType {
  public
    IntType() : ValueType(VTK_Int), width(width) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_Int;}
}

class StringType : public ValueType {
  public
    StringType() : ValueType(VTK_String) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_String;}
}

class CoreIRType : public ValueType {
  public
    CoreIRType() : ValueType(VTK_CoreIRType) {}
    static bool classof(const ValueType* v) {return v->getKind()==VTK_CoreIRType;}
}

}
#endif
