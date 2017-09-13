#include "coreir/libs/cgralib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(cgralib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_cgralib(Context* c) {
  
  Namespace* cgralib = c->newNamespace("cgralib");
  
  //Unary op declaration
  Params widthParams = {{"width",AINT}};
  cgralib->newTypeGen("unary",widthParams,[](Context* c, Args args) { 
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"in",c->BitIn()->Arr(width)},
      {"out",c->Bit()->Arr(width)},
    });
  });

  //PE declaration
  Params PEGenParams = {{"width",AINT},{"numbitports",AINT},{"numdataports",AINT}};
  Params PEConfigParams({
    {"op",ASTRING},
    {"LUT_init",AINT},
    {"data0_mode",ASTRING},
    {"data0_init",AINT},
    {"data1_mode",ASTRING},
    {"data1_init",AINT},
    {"bit0_mode",ASTRING},
    {"bit0_init",AINT},
    {"bit1_mode",ASTRING},
    {"bit2_mode",ASTRING}
  });
  cgralib->newTypeGen("PEType",PEGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint numdataports = args.at("numdataports")->get<ArgInt>();
    uint numbitports = args.at("numbitports")->get<ArgInt>();
    return c->Record({
      {"data",c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(numdataports)},
        {"out",c->Bit()->Arr(width)}
      })},
      {"bit",c->Record({
        {"in",c->BitIn()->Arr(numbitports)},
        {"out",c->Bit()}
      })}
    });
  });
  Generator* PE = cgralib->newGeneratorDecl("PE",cgralib->getTypeGen("PEType"),PEGenParams,PEConfigParams);
  PE->addDefaultGenArgs({{"width",c->argInt(16)},{"numdataports",c->argInt(2)},{"numbitports",c->argInt(3)}});
  PE->addDefaultConfigArgs({
      {"LUT_init",c->argInt(0)},
      {"data0_mode",c->argString("BYPASS")},
      {"data0_init",c->argInt(0)},
      {"data1_mode",c->argString("BYPASS")},
      {"data1_init",c->argInt(0)},
      {"bit0_mode",c->argString("BYPASS")},
      {"bit0_init",c->argInt(0)},
      {"bit1_mode",c->argString("BYPASS")},
      {"bit2_mode",c->argString("BYPASS")}
  });

  //DataPE declaration
  Params DataPEGenParams = {{"width",AINT},{"numdataports",AINT}};
  Params DataPEConfigParams({
    {"op",ASTRING},
    {"data0_mode",ASTRING},
    {"data0_init",AINT},
    {"data1_mode",ASTRING},
    {"data1_init",AINT}
  });

  cgralib->newTypeGen("DataPEType",DataPEGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint numdataports = args.at("numdataports")->get<ArgInt>();
    return c->Record({
      {"data",c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(numdataports)},
        {"out",c->Bit()->Arr(width)}
      })}
    });
  });
  Generator* DataPE = cgralib->newGeneratorDecl("DataPE",cgralib->getTypeGen("DataPEType"),DataPEGenParams,DataPEConfigParams);
  DataPE->addDefaultGenArgs({{"width",c->argInt(16)},{"numdataports",c->argInt(2)}});
  DataPE->addDefaultConfigArgs({
      {"data0_mode",c->argString("BYPASS")},
      {"data0_init",c->argInt(0)},
      {"data1_mode",c->argString("BYPASS")},
      {"data1_init",c->argInt(0)}
  });
  
  //BitPE declaration
  Params BitPEGenParams = {{"numbitports",AINT}};
  Params BitPEConfigParams({
    {"LUT_init",AINT},
    {"bit0_mode",ASTRING},
    {"bit0_init",AINT},
    {"bit1_mode",ASTRING},
    {"bit2_mode",ASTRING}
  });

  cgralib->newTypeGen("BitPEType",BitPEGenParams,[](Context* c, Args args) {
    uint numbitports = args.at("numbitports")->get<ArgInt>();
    return c->Record({
      {"bit",c->Record({
        {"in",c->BitIn()->Arr(numbitports)},
        {"out",c->Bit()}
      })}
    });
  });
  Generator* BitPE = cgralib->newGeneratorDecl("BitPE",cgralib->getTypeGen("BitPEType"),BitPEGenParams,BitPEConfigParams);
  BitPE->addDefaultGenArgs({{"numbitports",c->argInt(3)}});
  BitPE->addDefaultConfigArgs({
    {"bit0_mode",c->argString("BYPASS")},
    {"bit0_init",c->argInt(0)},
    {"bit1_mode",c->argString("BYPASS")},
    {"bit2_mode",c->argString("BYPASS")}
  });

  //IO Declaration
  Params modeParams = {{"mode",ASTRING}};
  cgralib->newGeneratorDecl("IO",cgralib->getTypeGen("unary"),widthParams,modeParams);
  cgralib->newModuleDecl("bitIO",c->Record({{"in",c->BitIn()},{"out",c->Bit()}}),modeParams);

  //Mem declaration
  Params MemGenParams = {{"width",AINT},{"depth",AINT}};
  Params MemConfigParams = {
    {"mode",ASTRING},
    {"fifo_depth",AINT},
    {"almost_full_cnt",AINT}
  };
  cgralib->newTypeGen("MemType",MemGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"addr", c->BitIn()->Arr(width)},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"ren", c->BitIn()},
      {"almost_full", c->Bit()},
      {"valid", c->Bit()}
    });
  });
  Generator* Mem = cgralib->newGeneratorDecl("Mem",cgralib->getTypeGen("MemType"),MemGenParams,MemConfigParams);
  Mem->addDefaultGenArgs({{"width",c->argInt(16)},{"depth",c->argInt(1024)}});
  Mem->addDefaultConfigArgs({
    {"fifo_depth",c->argInt(1024)},
    {"almost_full_cnt",c->argInt(0)}
  });



  return cgralib;
}


COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(cgralib)
