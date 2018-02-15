#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>

using namespace std;
using namespace CoreIR;

void Aetherling_createMapGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * This implementation of map is fully parallel. It will produce output in one clock cycle.
     * parallelOperatrs - how many operators to have in parallel
     * operator - the operator to parallelize. Note that it must have one input known as "in" and 
     * one output known as "out"
     */
    Params mapXTparams = Params({
            {"parallelOperators", c->Int()},
            {"operator", ModuleType::make(c)}
        });

    aetherlinglib->newTypeGen(
        "mapX_type", // name for typegen
        mapXTparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in")->Arr(parallelOperators)},
                    {"out", opType->sel("out")->Arr(parallelOperators)},
                    {"valid", c->Bit()}
                });
        });

    Generator* mapX =
        aetherlinglib->newGeneratorDecl("mapX", aetherlinglib->getTypeGen("mapX_type"), mapXTparams);

    mapX->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            assert(parallelOperators>0);
            
            // now create each op and wire the inputs and outputs to it
            for (uint i = 0; i < parallelOperators; i++) {
                string idxStr = to_string(i);                
                string opStr = "op_" + idxStr;
                def->addInstance(opStr, opModule);
                def->connect("self.in." + idxStr, opStr + ".in");
                def->connect(opStr + ".out", "self.out." + idxStr);
            }
        });
}
