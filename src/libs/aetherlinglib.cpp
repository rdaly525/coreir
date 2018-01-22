#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <vector>

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(aetherlinglib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_aetherlinglib(Context* c) {

    Namespace* aetherlinglib = c->newNamespace("aetherlinglib");

    /////////////////////////////////
    // Aetherlingliblib Types
    /////////////////////////////////

    Params widthparams = Params({{"width",c->Int()}});

    Params mapNparams = Params({
            {"width", c->Int()},
            {"parallelOperators", c->Int()},
            {"operator", c->String()}
        });

    aetherlinglib->newTypeGen(
        "mapN_type", // name for typegen
        mapNparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint width = genargs.at("width")->get<int>();
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            return c->Record({
                    {"in", c->BitIn()->Arr(width)->Arr(parallelOperators)},
                    {"out", c->Bit()->Arr(width)->Arr(parallelOperators)}
                });
        });

    Generator* mapN =
        aetherlinglib->newGeneratorDecl("mapN", aetherlinglib->getTypeGen("mapN_type"), mapNparams);

    mapN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint width = genargs.at("width")->get<int>();
            uint parallelOperators  = genargs.at("parallelOperators")->get<int>();
            string op = genargs.at("operator")->get<string>();
            assert(parallelOperators>0);
            assert(width>0);

            Const* aWidth = Const::make(c,width);
            
            // now create each op and wire the inputs and outputs to it
            for (int i = 0; i < parallelOperators; i++) {
                string idxStr = to_string(i);                
                string opStr = "op_" + idxStr;
                def->addInstance(opStr, op, {{"width", aWidth}});
                def->connect("self.in." + idxStr, opStr + ".in");
                def->connect(opStr + ".out", "self.out." + idxStr);
            }
             
        });

    return aetherlinglib;  
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(aetherlinglib)
