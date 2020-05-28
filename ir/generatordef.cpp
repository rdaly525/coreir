#include "ir/generatordef.h"
#include "ir/common.h"
#include "ir/generator.h"

namespace CoreIR {
void GeneratorDefFromFun::createModuleDef(ModuleDef* mdef, Values genargs) {
  checkValuesAreConst(genargs);
  moduledefgenfun(g->getContext(), genargs, mdef);
}
}  // namespace CoreIR
