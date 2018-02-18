#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>

using namespace std;
using namespace CoreIR;

/*
 * Create a map where all the results are computed in one clock cycle
 */
void defineFullyParallelMap(Context* c, ModuleDef* def, string mapName, uint numInputs, Module* opModule) {
    // now create each op and wire the inputs and outputs to it
    for (uint i = 0; i < parallelOperators; i++) {
        string idxStr = to_string(i);                
        string opStr = "op_" + idxStr;
        def->addInstance(opStr, opModule);
        def->connect("self.in." + idxStr, opStr + ".in");
        def->connect(opStr + ".out", "self.out." + idxStr);
    }
    string oneConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
    def->connect(oneConst + ".out", "self.valid");
}

void Aetherling_createMapGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * This type is for all maps, from fully sequential to fully parallel
     * parallelOperatrs - how many operators to have in parallel
     * operator - the operator to parallelize. Note that it must have one input known as "in" and 
     * one output known as "out"
     * parallelism - number of inputs to processes in one cycle. At this time, numInputs % parallelism == 0
     */
    Params mapParams = Params({
            {"numInputs", c->Int()},
            {"operator", ModuleType::make(c)},
            {"parallelism", c->Int()}
        });

    /*
     * All versions of map take the entire input in at once and emit a valid signal when the output is correct.
     * This is done to keep a consistent type interface so compiler transformations are easier.
     */
    aetherlinglib->newTypeGen(
        "map_type", // name for typegen
        mapParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in")->Arr(numInputs)},
                    {"out", opType->sel("out")->Arr(numInputs)},
                    {"valid", C->Bit()}
                });
        });

    Generator* map =
        aetherlinglib->newGeneratorDecl("map", aetherlinglib->getTypeGen("map_type"), mapParams);

    mapX->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            uint parallelism = genargs.at("parallelism")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            assert(parallelOperators>0);
            
            
        });

    /* 
     * This implementation of map is fully sequential, it will take the input in over cycles
     * equal to length of input 
     */
    Generator* mapT =
        aetherlinglib->newGeneratorDecl("mapT", aetherlinglib->getTypeGen("mapT_type"), mapXTparams);

    mapT->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            assert(parallelOperators>0);

            string serializerName = "serializeMapTInput";
            def->addInstance(serializerName, "commonlib.serializer", {
                    {"width", Const::make(c, 
            
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
