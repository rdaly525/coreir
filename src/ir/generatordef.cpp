#include "coreir/ir/generatordef.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/common.h"

namespace CoreIR {
void GeneratorDefFromFun::createModuleDef(ModuleDef* mdef, Values genargs) {
  checkValuesAreConst(genargs);
  moduledefgenfun(g->getContext(),genargs,mdef);
}
}

