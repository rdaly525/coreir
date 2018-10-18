#ifndef COREIR_AETHERLINGLIB_H_
#define COREIR_AETHERLINGLIB_H_

#include "coreir/common-macros.h"
#include "coreir-c/ctypes.h"

#ifdef __cplusplus
#include "coreir.h"
COREIR_GEN_CPP_API_DECLARATION_FOR_LIBRARY(aetherlinglib);
#endif

COREIR_GEN_C_API_DECLARATION_FOR_LIBRARY(aetherlinglib);

const std::string AETHERLING_NAMESPACE = "aetherlinglib";

void Aetherling_createMapGenerator(CoreIR::Context* c);
void Aetherling_createReduceGenerator(CoreIR::Context* c);
void Aetherling_createZipGenerator(CoreIR::Context* c);
void Aetherling_createConvGenerator(CoreIR::Context* c);
void Aetherling_createFlattenGenerator(CoreIR::Context* c);
void Aetherling_createHydrateAndDehydrateGenerators(CoreIR::Context* c);
void Aetherling_createStreamifyArrayifyGenerator(CoreIR::Context* c);
void Aetherling_createOverlapPartitionGenerator(CoreIR::Context* c);

// helper functions
std::string Aetherling_addCoreIRConstantModule(CoreIR::Context* c, CoreIR::ModuleDef* def, uint width, CoreIR::Const* val);
CoreIR::Module* Aetherling_convert2InputModuleTo2ZippedInput(CoreIR::Context* c, CoreIR::Module* moduleToWrap, CoreIR::Values modargs=CoreIR::Values());


#endif //COREIR_AETHERLINGLIB_HPP_
