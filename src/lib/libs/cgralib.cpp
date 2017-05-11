#include "coreir-lib/cgralib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(cgralib);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_cgralib(Context* c) {
  
  Namespace* cgralib = c->newNamespace("cgra");
  
  //Unary op declaration
  Params widthParams = {{"width",AINT}};
  cgralib->newTypeGen("UnaryType",widthParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"in",c->BitIn()->Arr(width)},
      {"out",c->Bit()->Arr(width)},
    });
  });

  //PE declaration
  Params PEGenParams = {{"width",AINT},{"numin",AINT}};
  Params opParams = {{"op",ASTRING}};
  cgralib->newTypeGen("PEType",PEGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint numin = args.at("numin")->get<ArgInt>();
    return c->Record({
      {"data",c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(numin)},
        {"out",c->Bit()->Arr(width)}
      })},
      {"bit",c->Record({
        {"in",c->BitIn()->Arr(numin)},
        {"out",c->Bit()}
      })}
    });
  });
  cgralib->newGeneratorDecl("PE",cgralib->getTypeGen("PEType"),PEGenParams,opParams);

  //Const Declaration
  Params valueParams = {{"value",AINT}};
  cgralib->newTypeGen("SrcType",widthParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"out",c->Bit()->Arr(width)}
    });
  });
  cgralib->newGeneratorDecl("Const",cgralib->getTypeGen("SrcType"),widthParams,valueParams);

  //Reg declaration
  cgralib->newGeneratorDecl("Reg",cgralib->getTypeGen("UnaryType"),widthParams);

  //IO Declaration
  Params modeParams = {{"mode",ASTRING}};
  cgralib->newGeneratorDecl("IO",cgralib->getTypeGen("UnaryType"),widthParams,modeParams);

  //Mem declaration
  Params MemGenParams = {{"width",AINT},{"depth",AINT}};
  cgralib->newTypeGen("MemType",MemGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    //TODO for simplicity just make the address width 16 as well
    return c->Record({
      {"read",c->Record({
        {"data",c->Bit()->Arr(width)},
        {"addr",c->BitIn()->Arr(width)},
        {"en",c->BitIn()},
        {"empty",c->Bit()}
      })},
      {"write",c->Record({
        {"data",c->BitIn()->Arr(width)},
        {"addr",c->BitIn()->Arr(width)},
        {"en",c->BitIn()},
        {"full",c->Bit()}
      })}
    });
  });
  cgralib->newGeneratorDecl("Mem",cgralib->getTypeGen("MemType"),MemGenParams,modeParams);

  return cgralib;
}
