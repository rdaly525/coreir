#ifndef COREIR_GENERATORDEF_HPP_
#define COREIR_GENERATORDEF_HPP_

#include "fwd_declare.h"
#include "common.h"

namespace CoreIR {
class GeneratorDef {
  protected:
    Generator* g;
  public: 
    GeneratorDef(Generator* g) : g(g) {}
    virtual ~GeneratorDef() {}
    virtual void createModuleDef(ModuleDef*,Values) = 0;
};

class GeneratorDefFromFun : public GeneratorDef {
  public:
    GeneratorDefFromFun(Generator* g, ModuleDefGenFun moduledefgenfun) : GeneratorDef(g), moduledefgenfun(moduledefgenfun) {}
    void createModuleDef(ModuleDef* mdef, Values genargs) override {
      checkValuesAreConst(genargs);
      moduledefgenfun(g->getContext(),genargs,mdef);
    }
  protected:
    ModuleDefGenFun moduledefgenfun;

};

} //CoreIR namespace
#endif //GENERATORDEF_HPP_
