#include "coreir/libs/aetherlinglib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(commonlib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_commonlib(Context* c) {

  Namespace* commonlib = c->newNamespace("commonlib");
  Namespace* coreirprims = c->getNamespace("coreir");

  /////////////////////////////////
  // Commonlib Types
  /////////////////////////////////

  Params widthparams = Params({{"width",c->Int()}});

  commonLib->newTypeGen(
      "mapN_type", // name for typegen
      {
          {"width", c->Int()},
          {"N", c->Int()},
          {"numOperatorsParallel", c->Int()},
          {"operator", c->String()}
      }, // generator parameters
      [](Context* c, Values genargs) { //Function to compute type
          uint width = genargs.at("width")->get<int>();
          uint N = genargs.at("N")->get<int>();
          uint numOperatorsParallel = genargs.at("N")->get<int>();
          return c->Record({
                  {"in", c->BitIn()->Arr(width)->Arr(N)}
                  {"out", c->Bit()->Arr(width)}
              });
      });

  
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(aetherlinglib)
