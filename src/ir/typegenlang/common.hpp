#ifndef TYPELANG_COMMON_HPP_
#define TYPELANG_COMMON_HPP_

#include "typegenlang.hpp"

template<typename V>
class VConst : public VExpr<V> {
  V value;
  public :
    VConst(V value) : value(value) {}
    V eval(Context* c, Args args) {
      return value;
    }
};

template<typename V>
class VSelect : public VExpr<V> {
  VBool* sel;
  VExpr<V>* valTrue;
  VExpr<V>* valFalse;
  public :
    VSelect(VBool* sel, VExpr<V>* valTrue, VExpr<V>* valFalse) : sel(sel), valTrue(valTrue), valFalse(valFalse) {}
    ~VSelect() {
      delete sel;
      delete valTrue;
      delete valFalse;
    }
    V eval(Context* c, Args args) {
      if (sel->eval(c,args)) {
        return valTrue->eval(c,args);
      }
      else {
        return valFalse->eval(c,args);
      }
    }
};

template<typename V>
class VArg : public VExpr<V> {
  std::string key;
  typedef typename Val2Arg<V>::type ArgTy;
  public :
    VArg(std::string key) : key(key) {}
    V eval(Context* c, Args args) {
      ASSERT(args.count(key)>0,"Arg cannot be found: " + key);
      Arg* val = args[key];
      ASSERT(isa<ArgTy>(val),"Arg \"" + key + "\" is not a correct type!");
      return val->get<ArgTy>();
    }
};

template<typename V>
class VEq : public VBool {
  typedef typename Val2V<V>::type VTy;
  VTy* left;
  VTy* right;
  public :
    VEq(VTy* left, VTy* right) : left(left), right(right) {}
    ~VEq() {
      delete left;
      delete right;
    }
    bool eval(Context* c, Args args) {
      return left->eval(c,args) == right->eval(c,args);
    }
};

#endif
