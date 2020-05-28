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
                                 {"O", c->Bit()}});
  Params SB_LUT4Params({{"LUT_INIT", c->BitVector(16)}});
  ice40->newModuleDecl("SB_LUT4", SB_LUT4Type, SB_LUT4Params);

  Type* SB_CARRYType = c->Record({{"I0", c->BitIn()},
                                  {"I1", c->BitIn()},
                                  {"CI", c->BitIn()},
                                  {"CO", c->Bit()}});
  ice40->newModuleDecl("SB_CARRY", SB_CARRYType);

  Type* SB_DFFType = c->Record(
    {{"C", c->Named("coreir.clkIn")}, {"D", c->BitIn()}, {"Q", c->Bit()}});
  ice40->newModuleDecl("SB_DFF", SB_DFFType);

  Type* SB_DFFEType = c->Record({{"C", c->Named("coreir.clkIn")},
                                 {"D", c->BitIn()},
                                 {"E", c->BitIn()},
                                 {"Q", c->Bit()}});
  ice40->newModuleDecl("SB_DFFE", SB_DFFEType);

  Type* SB_RAM40_4KType = c->Record({{"RDATA", c->Bit()->Arr(16)},
                                     {"RADDR", c->BitIn()->Arr(11)},
                                     {"RCLK", c->Named("coreir.clkIn")},
                                     {"RCLKE", c->BitIn()},
                                     {"RE", c->BitIn()},
                                     {"WCLK", c->Named("coreir.clkIn")},
                                     {"WCLKE", c->BitIn()},
                                     {"WE", c->BitIn()},
                                     {"WADDR", c->BitIn()->Arr(11)},
                                     {"MASK", c->BitIn()->Arr(16)},
                                     {"WDATA", c->BitIn()->Arr(16)}});
  Params SB_RAM40_4KParams({{"READ_MODE", c->Int()}, {"WRITE_MODE", c->Int()}});
  for (int i = 0; i < 16; i++) {
    ostringstream o;
    o << "INIT_" << uppercase << hex << i;
    SB_RAM40_4KParams[o.str()] = c->BitVector(256);
  }
  ice40->newModuleDecl("SB_RAM40_4K", SB_RAM40_4KType, SB_RAM40_4KParams);

  Type* SB_PLL40_COREType = c->Record(
    {{"BYPASS", c->BitIn()},
     {"PLLOUTCORE", c->Bit()},
     {"PLLOUTGLOBAL", c->Named("coreir.clk")},
     {"REFERENCECLK", c->Named("coreir.clkIn")},
     {"RESETB", c->BitIn()}});
  Params SB_PLL40_COREParams({{"DIVF", c->BitVector(7)},
                              {"DIVQ", c->BitVector(3)},
                              {"DIVR", c->BitVector(4)},
                              {"FEEDBACK_PATH", c->String()},
                              {"FILTER_RANGE", c->BitVector(3)},
                              {"PLLOUT_SELECT", c->String()}});
  ice40->newModuleDecl("SB_PLL40_CORE", SB_PLL40_COREType, SB_PLL40_COREParams);

  return ice40;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(ice40)
