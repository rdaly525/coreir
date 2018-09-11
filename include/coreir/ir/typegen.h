#ifndef COREIR_TYPEGEN_HPP_
#define COREIR_TYPEGEN_HPP_

#include "fwd_declare.h"
#include "globalvalue.h"

namespace CoreIR {

class TypeGen : public GlobalValue {
  std::map<Values,Type*,ValuesComp> typeCache;
  Params params;
  bool flipped;
  
  protected : 
    TypeGen(Namespace* ns, std::string name, Params params, bool flipped=false) : GlobalValue(GVK_TypeGen,ns,name), params(params), flipped(flipped) {}
    virtual Type* createType(Values args) = 0;
  
  public :
    virtual ~TypeGen() {}
    // This function should return whether this typegen can return a type if passed these args.
    virtual bool hasType(Values args) = 0;
    //Returns the Type as a function of the args
    virtual Type* getType(Values genargs) final;
    Params getParams() const {return params;}
    const std::map<Values,Type*,ValuesComp>& getCached() { return typeCache;}
    bool isFlipped() const { return flipped;}
    virtual std::string toString() const override = 0;
    virtual void print() const override {std::cout << this->toString() << std::endl;}
};

//Notice, the base class does the flipping for you in the function computeType
class TypeGenFromFun : public TypeGen {
  protected :
    TypeGenFun fun;
    TypeGenFromFun(Namespace* ns, std::string name, Params params, TypeGenFun fun, bool flipped) : TypeGen(ns,name,params,flipped), fun(fun) {}
    Type* createType(Values genargs) override {
      return fun(this->getContext(),genargs);
    }
  public :
    bool hasType(Values genargs) override;
    std::string toString() const override;
    
    //Creation function
    static TypeGenFromFun* make(Namespace* ns, std::string name, Params genparams, TypeGenFun fun,bool flipped=false);
};

class TypeGenSparse : public TypeGen {
  protected :
    std::map<Values,Type*,ValuesComp> typeLookup;
    TypeGenSparse(Namespace* ns, std::string name, Params params, std::vector<std::pair<Values,Type*>>& typelist );
  public :
    Type* createType(Values genargs) override;
    bool hasType(Values genargs) override;
    std::string toString() const override;
    
    //Creation function
    static TypeGenSparse* make(Namespace* ns, std::string name, Params params, std::vector<std::pair<Values,Type*>>& typelist);
};

//TODO could potentially turn into singlton?
//This is used for 'blank' typegens.
//createType always fails
//hasType always returns false
//This allows the existence of generators with functionally no typegen
class TypeGenImplicit : public TypeGen {
  protected :
    TypeGenImplicit(Namespace* ns, std::string name, Params params) : TypeGen(ns,name,params,false) {}
  public :
    Type* createType(Values genargs) override;
    bool hasType(Values genargs) override;
    std::string toString() const override;
    
    //Creation function
    static TypeGenImplicit* make(Namespace* ns, std::string name, Params params);
};



}// CoreIR
#endif //TYPEGEN_HPP_
