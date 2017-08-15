#include "coreir-lib/ice40.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(ice40);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_ice40(Context* c) {
    Namespace* ice40 = c->newNamespace("ice40");
    Type* SB_LUT4Type = c->Record({{"I0", c->BitIn()},
                                   {"I1", c->BitIn()},
                                   {"I2", c->BitIn()},
                                   {"I3", c->BitIn()},
                                   {"O",  c->Bit()}});
    Params SB_LUT4Params({{"INIT", AINT}});
    ice40->newModuleDecl("SB_LUT4", SB_LUT4Type, SB_LUT4Params);
    return ice40;
}
