#ifndef COREIR_GENERATOR_HPP_
#define COREIR_GENERATOR_HPP_


#include "fwd_declare.h"
#include "globalvalue.h"

namespace CoreIR {

class Generator : public GlobalValue {
    
  TypeGen* typegen;
  
  Params genparams;
  Values defaultGenArgs; 
  
  ModParamsGenFun modParamsGen=nullptr;

  //This is memory managed
  std::map<Values,Module*,ValuesComp> genCache;
  GeneratorDef* def = nullptr;
  
  public :
    Generator(Namespace* ns,std::string name,TypeGen* typegen, Params genparams);
    virtual ~Generator();
    static bool classof(const GlobalValue* i) {return i->getKind()==GVK_Generator;}
    std::string toString() const override;
    void print() const override;
    TypeGen* getTypeGen() const { return typegen;}
    bool hasDef() const { return !!def; }
    GeneratorDef* getDef() const {return def;}
    
    //This will create a fully run module
    //Note, this is stored in the generator itself and is not in the namespace
    Module* getModule(Values genargs);
    
    //This will create a new generated module with the specified type.
    //If the typegen can create a type, it will verify types match, else it will just use the type
    Module* getModule(Values genargs, Type* type);
    
    //Will delete the cached Module
    void eraseModule(Values genargs);

    //Get all generated modules
    std::map<std::string,Module*> getGeneratedModules();
   
    bool runAll();

    //This will transfer memory management of def to this Generator
    void setDef(GeneratorDef* def) { assert(!this->def); this->def = def;}
    void setGeneratorDefFromFun(ModuleDefGenFun fun);
    Params getGenParams() {return genparams;}

    //This will add (and override) default args
    void addDefaultGenArgs(Values defaultGenargs);
    Values getDefaultGenArgs() { return defaultGenArgs;}
  
    void setModParamsGen(ModParamsGenFun mpg) {modParamsGen = mpg;}
    void setModParamsGen(Params modparams,Values defaultModArgs=Values()) {
      this->modParamsGen = [modparams,defaultModArgs](Context* c,Values genargs) mutable -> std::pair<Params,Values> {
        return {modparams,defaultModArgs}; 
      };
    }
    std::pair<Params,Values> getModParams(Values genargs) {
      if (modParamsGen) {
        return modParamsGen(getContext(),genargs);
      }
      else {
        return {Params(),Values()};
      }
    }
};

}//CoreIR namespace

#endif 
