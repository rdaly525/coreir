#ifndef COREIR_GENERATORDEF_HPP_
#define COREIR_GENERATORDEF_HPP_

#include "fwd_declare.hpp"

namespace CoreIR {
class GeneratorDef {
  protected:
    Generator* g;
  public: 
    GeneratorDef(Generator* g) : g(g) {}
    virtual ~GeneratorDef() {}
    virtual void createModuleDef(ModuleDef*,Context*, Type*, Args) = 0;
};

class GeneratorDefFromFun : public GeneratorDef {
  protected:
    ModuleDefGenFun moduledefgenfun;
  public:
    GeneratorDefFromFun(Generator* g, ModuleDefGenFun moduledefgenfun) : GeneratorDef(g), moduledefgenfun(moduledefgenfun) {}
    void createModuleDef(ModuleDef* mdef, Context* c, Type* t, Args args) {
      moduledefgenfun(mdef,c,t,args);
    }
};

} //CoreIR namespace
#endif //GENERATORDEF_HPP_
