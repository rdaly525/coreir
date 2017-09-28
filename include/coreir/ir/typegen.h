#ifndef COREIR_TYPEGEN_HPP_
#define COREIR_TYPEGEN_HPP_

#include "fwd_declare.h"

namespace CoreIR {

class TypeGen : public RefName {
  Params params;
  bool flipped;
  //TODO maybe cache the types based off the args
  public:
    TypeGen(Namespace* ns, std::string name, Params params, bool flipped=false) : RefName(ns,name), params(params), flipped(flipped) {}
    virtual ~TypeGen() {}
    virtual Type* createType(Context* c, Values args) = 0;
    Type* getType(Consts genargs); //TODO change this to a functor
    Params getParams() const {return params;}
    bool isFlipped() const { return flipped;}
};

//Notice, the base class does the flipping for you in the function computeType
class TypeGenFromFun : public TypeGen {
  public :
    typedef Type* (*TypeGenFun)(Context* c, Consts genargs);
    TypeGenFromFun(Namespace* ns, std::string name, Params params, TypeGenFun fun, bool flipped=false) : TypeGen(ns,name,params,flipped), fun(fun) {}
    Type* createType(Context* c, Consts genargs) {
      return fun(c,genargs);
    }
  private :
    TypeGenFun fun;
};

}// CoreIR
#endif //TYPEGEN_HPP_
