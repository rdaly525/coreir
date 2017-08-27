#include "coreir-lib/common.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(common);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_common(Context* c) {
  Namespace* common = c->newNamespace("common");

  //Add a LUTN
  Params lutNParams({{"N",AINT}});
  common->newTypeGen("lutNType",lutNParams,[](Context* c, Args args) { 
    uint N = args.at("N")->get<ArgInt>();
    ASSERT(N<=5,"NYI due to init bit length");
    return c->Record({
      {"in",c->BitIn()->Arr(N)},
      {"out",c->Bit()}
    });
  });
  Generator* lutN = common->newGeneratorDecl("lutN",common->getTypeGen("lutNType"),lutNParams,{{"init",AINT}});
  lutN->addDefaultConfigArgs({{"init",c->argInt(0)}});
  
  return common;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(common)
