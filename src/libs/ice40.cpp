#include "coreir/libs/ice40.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(ice40);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_ice40(Context* c) {
    Namespace* ice40 = c->newNamespace("ice40");
    
    Type* SB_LUT4Type = c->Record({{"I0", c->BitIn()},
                                   {"I1", c->BitIn()},
                                   {"I2", c->BitIn()},
                                   {"I3", c->BitIn()},
                                   {"O",  c->Bit()}});
    Params SB_LUT4Params({{"LUT_INIT", c->BitVector(16)}});
    ice40->newModuleDecl("SB_LUT4", SB_LUT4Type, SB_LUT4Params);

    Type* SB_CARRYType = c->Record({{"I0", c->BitIn()},
                                    {"I1", c->BitIn()},
                                    {"CI", c->BitIn()},
                                    {"CO",  c->Bit()}});
    ice40->newModuleDecl("SB_CARRY", SB_CARRYType);

    Type* SB_DFFType = c->Record({{"C", c->Named("coreir.clkIn")},
                                  {"D", c->BitIn()},
                                  {"Q", c->Bit()}});
    ice40->newModuleDecl("SB_DFF", SB_DFFType);

    Type* SB_DFFEType = c->Record({{"C", c->Named("coreir.clkIn")},
                                   {"D", c->BitIn()},
                                   {"E", c->BitIn()},
                                   {"Q", c->Bit()}});
    ice40->newModuleDecl("SB_DFFE", SB_DFFEType);

    return ice40;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(ice40)
