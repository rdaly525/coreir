#include "coreir/libs/commonlib.h"
#include <algorithm>  // std::max

#include "coreir/ir/context.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/value.h"
#include "coreir/ir/generator.h"

// This file is just included in context.cpp

using namespace std;
using namespace CoreIR;


bool isPowerOfTwo(const uint n) {
  if (n == 0) { return 0; }

  return (n & (n - 1)) == 0;
}

COREIR_GEN_HEADER(memory) {
  Namespace* memory = c->newNamespace("memory");

  // Note this is a linebuffer MEMORY (a single row), with a stencil valid
  Params RbwsvGenParams = {{"width", c->Int()},
                           {"depth", c->Int()},
                           {"stencil_width", c->Int()}};
  memory->newTypeGen(
    "rowbufferWithStencilValidType",
    RbwsvGenParams,
    [](Context* c, Values genargs) {
      uint width = genargs.at("width")->get<int>();
      return c->Record({
        {"clk", c->Named("coreir.clkIn")},
        {"wdata", c->BitIn()->Arr(width)},
        {"wen", c->BitIn()},
        {"rdata", c->Bit()->Arr(width)},
        {"valid", c->Bit()},
        {"flush", c->BitIn()},
      });
    });
  memory->newGeneratorDecl(
    "rowbuffer_stencil_valid",
    memory->getTypeGen("rowbufferWithStencilValidType"),
    RbwsvGenParams);

  Params MemGenParams = {{"width", c->Int()}, {"depth", c->Int()}};
  // Linebuffer Memory. Use this for memory in linebuffer mode
  memory->newTypeGen(
    "rowbufferType",
    MemGenParams,
    [](Context* c, Values genargs) {
      uint width = genargs.at("width")->get<int>();
      return c->Record({
        {"clk", c->Named("coreir.clkIn")},
        {"wdata", c->BitIn()->Arr(width)},
        {"wen", c->BitIn()},
        {"rdata", c->Bit()->Arr(width)},
        {"valid", c->Bit()},
        {"flush", c->BitIn()},
      });
    });

  // Note this is a linebuffer MEMORY (a single row) and not a full linebuffer.
  memory->newGeneratorDecl(
    "rowbuffer",
    memory->getTypeGen("rowbufferType"),
    MemGenParams);


  // Fifo Memory. Use this for memory in Fifo mode
  memory->newTypeGen(
    "FifoMemType",
    MemGenParams,
    [](Context* c, Values genargs) {
      uint width = genargs.at("width")->get<int>();
      return c->Record({{"clk", c->Named("coreir.clkIn")},
                        {"wdata", c->BitIn()->Arr(width)},
                        {"wen", c->BitIn()},
                        {"rdata", c->Bit()->Arr(width)},
                        {"ren", c->BitIn()},
                        {"almost_full", c->Bit()},
                        {"valid", c->Bit()}});
    });
  Generator* fifoMem = memory->newGeneratorDecl(
    "fifo",
    memory->getTypeGen("FifoMemType"),
    MemGenParams);
  fifoMem->addDefaultGenArgs(
    {{"width", Const::make(c, 16)}, {"depth", Const::make(c, 1024)}});
  fifoMem->setModParamsGen({{"almost_full_cnt", c->Int()}});

  memory->newTypeGen("RamType", MemGenParams, [](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    uint depth = genargs.at("depth")->get<int>();
    uint awidth = (uint)ceil(log2(depth));
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"waddr", c->BitIn()->Arr(awidth)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"raddr", c->BitIn()->Arr(awidth)},
      {"ren", c->BitIn()},
    });
  });

  // This has a 1 cycle read delay
  // TODO describe the read after write behavior
  // TODO add in parameterized read after write behavior and the read delay
  memory->newGeneratorDecl(
    "ram",
    memory->getTypeGen("RamType"),
    MemGenParams);

  memory->newTypeGen("RamType2", MemGenParams, [](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"waddr", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"raddr", c->BitIn()->Arr(width)},
      {"ren", c->BitIn()},
    });
  });

  // This has a 1 cycle read delay
  // TODO describe the read after write behavior
  // TODO add in parameterized read after write behavior and the read delay
  memory->newGeneratorDecl(
    "ram2",
    memory->getTypeGen("RamType2"),
    MemGenParams);

  // ROM= Read-only memory. Index to read values from memory, but no exposed
  // write port.
  Params RomGenParams = {{"width", c->Int()}, {"depth", c->Int()}};
  auto RomModParamFun =
    [](Context* c, Values genargs) -> std::pair<Params, Values> {
    Params modparams;
    Values defaultargs;
    modparams["init"] = JsonType::make(c);
    return {modparams, defaultargs};
  };

  memory->newTypeGen("RomType", MemGenParams, [](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    uint depth = genargs.at("depth")->get<int>();
    uint awidth = std::max((int)ceil(log2(depth)), 1);
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"rdata", c->Bit()->Arr(width)},
      {"raddr", c->BitIn()->Arr(awidth)},
      {"ren", c->BitIn()},
    });
  });

  Generator* rom = memory->newGeneratorDecl(
    "rom",
    memory->getTypeGen("RomType"),
    MemGenParams);
  rom->setModParamsGen(RomModParamFun);

  // ROM= Read-only memory. Index to read values from memory, but no exposed
  // write port.
  //  This ROM differs in read address size, and maintains a consistent 16 bits
  //  for ease of connecting to other modules with a constant bitwidth.
  memory->newTypeGen("Rom2Type", MemGenParams, [](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"rdata", c->Bit()->Arr(width)},
      {"raddr", c->BitIn()->Arr(width)},
      {"ren", c->BitIn()},
    });
  });

  Generator* rom2 = memory->newGeneratorDecl(
    "rom2",
    memory->getTypeGen("Rom2Type"),
    MemGenParams);
  rom2->setModParamsGen(RomModParamFun);

  // SyncReadMemory
  Params syncReadMemGenParams(
    {{"width", c->Int()}, {"depth", c->Int()}, {"has_init", c->Bool()}});
  auto syncReadMemFun = [](Context* c, Values genargs) {
    int width = genargs.at("width")->get<int>();
    int depth = genargs.at("depth")->get<int>();
    int awidth = std::max((int)ceil(std::log2(depth)), 1);
    return c->Record(
      {{"clk", c->Named("coreir.clkIn")},
       {"wdata", c->BitIn()->Arr(width)},
       {"waddr", c->BitIn()->Arr(awidth)},
       {"wen", c->BitIn()},
       {"rdata", c->Bit()->Arr(width)},
       {"ren", c->BitIn()},
       {"raddr", c->BitIn()->Arr(awidth)}});
  };

  auto syncReadMemModParamFun =
    [](Context* c, Values genargs) -> std::pair<Params, Values> {
    Params modparams;
    Values defaultargs;
    bool has_init = genargs.at("has_init")->get<bool>();
    if (has_init) { modparams["init"] = JsonType::make(c); }
    return {modparams, defaultargs};
  };

  TypeGen* syncReadMemTypeGen = memory->newTypeGen(
    "syncReadMemType",
    syncReadMemGenParams,
    syncReadMemFun);

  Generator* syncReadMem = memory->newGeneratorDecl(
    "sync_read_mem",
    syncReadMemTypeGen,
    syncReadMemGenParams);
  syncReadMem->setModParamsGen(syncReadMemModParamFun);
  syncReadMem->addDefaultGenArgs({{"has_init", Const::make(c, false)}});
}
