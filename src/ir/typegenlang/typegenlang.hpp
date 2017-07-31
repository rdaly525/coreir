#ifndef TYPELANG_HPP_
#define TYPELANG_HPP_

#include "coreir.h"

using namespace CoreIR;

template<typename V>
class VExpr {
  public :
    typedef V RetTy;
    VExpr() {}
    virtual ~VExpr() {}
    virtual V eval(Context* c, Args args) = 0;
};

using VBool = VExpr<bool>;
using VInt = VExpr<int>;
using VType = VExpr<Type*>;

class TypeGenLang : public TypeGen {
  
  VType* vtype;
  public:
    TypeGenLang(Namespace* ns, string name, Params params, VType* vtype, bool flipped=false) : TypeGen(ns,name,params,flipped), vtype(vtype) {
      assert(vtype);
    }
    ~TypeGenLang() {delete vtype;}
    Type* createType(Context* c, Args args) {
      return vtype->eval(c,args);
    }
};

template<class V>
struct Val2V;

#define VAL2V_SPECIALIZE(valtype,vtype) \
template<> \
struct Val2V<valtype> { \
  typedef vtype type; \
};

VAL2V_SPECIALIZE(bool,VBool);
VAL2V_SPECIALIZE(int,VInt);
VAL2V_SPECIALIZE(CoreIR::Type*,VType);

#undef VAL2V_SPECIALIZE

#endif
