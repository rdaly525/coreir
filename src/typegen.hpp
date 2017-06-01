#ifndef TYPEGEN_HPP_
#define TYPEGEN_HPP_

#include "common.hpp"

namespace CoreIR {

class TypeGen {
  Namespace* ns;
  string name;
  Params params;
  bool flipped;
  
  //TODO maybe cache the types based off the args
  public:
    TypeGen(Namespace* ns, string name, Params params, bool flipped=false) : ns(ns), name(name), params(params), flipped(flipped) {}
    virtual ~TypeGen() {}
    virtual Type* createType(Context* c, Args args) = 0;
    Type* getType(Args args) {
      assert(checkArgs(args,params));
      Type* t = createType(ns->getContext(),args);
      return flipped ? t->getFlipped() : t;
    }
    Namespace* getNamespace() const {return ns;}
    const string& getName() const {return name;}
    Params getParams() const {return params;}
    bool isFlipped() const { return flipped;}
};

//Notice, the base class does the flipping for you in the function computeType
class TypeGenFromFun : public TypeGen {
  TypeGenFun fun;
  
  public:
    TypeGenFromFun(Namespace* ns, string name, Params params, TypeGenFun fun, bool flipped=false) : TypeGen(ns,name,params,flipped), fun(fun) {}
    Type* createType(Context* c, Args args) {
      return fun(c,args);
    }
};

}// CoreIR
#endif //TYPEGEN_HPP_
