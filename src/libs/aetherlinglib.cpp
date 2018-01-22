#include "coreir/libs/aetherlinglib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(aetherlinglib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_aetherlinglib(Context* c) {

  Namespace* aetherlinglib = c->newNamespace("aetherlinglib");
  //Namespace* coreirprims = c->getNamespace("coreir");

  /////////////////////////////////
  // Commonlib Types
  /////////////////////////////////

  Params widthparams = Params({{"width",c->Int()}});

  Params mapNparams = Params({
          {"width", c->Int()},
          {"N", c->Int()},
          {"numOperatorsParallel", c->Int()},
          {"operator", c->String()}
      });

  aetherlinglib->newTypeGen(
      "mapN_type", // name for typegen
      mapNparams, // generator parameters
      [](Context* c, Values genargs) { //Function to compute type
          uint width = genargs.at("width")->get<int>();
          uint N = genargs.at("N")->get<int>();
          return c->Record({
                  {"in", c->BitIn()->Arr(width)->Arr(N)},
                  {"out", c->Bit()->Arr(width)}
              });
      });

  aetherlinglib->newGeneratorDecl("mapN", aetherlinglib->getTypeGen("mapN_type"), mapNparams);

  return aetherlinglib;  
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(aetherlinglib)
