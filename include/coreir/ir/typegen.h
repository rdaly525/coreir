#ifndef COREIR_TYPEGEN_HPP_
#define COREIR_TYPEGEN_HPP_

#include "fwd_declare.h"
#include "globalvalue.h"

namespace CoreIR {

class TypeGen : public GlobalValue {
  Params params;
  bool flipped;
  //TODO maybe cache the types based off the args
  public:
    TypeGen(Namespace* ns, std::string name, Params params, bool flipped=false) : GlobalValue(GVK_TypeGen,ns,name), params(params), flipped(flipped) {}
    virtual ~TypeGen() {}
    virtual Type* createType(Context* c, Values args) = 0;
    virtual std::string toString() const override = 0;
    virtual void print() const override = 0;
    Type* getType(Values genargs); //TODO change this to a functor
    Params getParams() const {return params;}
    bool isFlipped() const { return flipped;}
};

//Notice, the base class does the flipping for you in the function computeType
class TypeGenFromFun : public TypeGen {
  public :
    TypeGenFromFun(Namespace* ns, std::string name, Params params, TypeGenFun fun, bool flipped=false) : TypeGen(ns,name,params,flipped), fun(fun) {}
    Type* createType(Context* c, Values genargs) override {
      return fun(c,genargs);
    }
    std::string toString() const override {return "NYI"; }
    void print() const override {}//TODO
  private :
    TypeGenFun fun;
};

}// CoreIR
#endif //TYPEGEN_HPP_
