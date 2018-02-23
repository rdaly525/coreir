#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>

using namespace std;
using namespace CoreIR;

/*
 * Create a map where all the results are computed in one clock cycle
 */
void defineFullyParallelMap(Context* c, ModuleDef* def, string mapName, uint numInputs, Module* opModule) {
   
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
                    {"ready", c->Bit()},
                    {"nextReady", c->BitIn()},
                    {"valid", c->Bit()},
                    {"prevValid", c->BitIn()}
                });
        });

    Generator* mapParallel =
        aetherlinglib->newGeneratorDecl("mapParallel", aetherlinglib->getTypeGen("map_type"), mapParams);

    mapParallel->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            uint parallelism = genargs.at("parallelism")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();

            // now create each op and wire the inputs and outputs to it
            for (uint i = 0; i < parallelOperators; i++) {
                string idxStr = to_string(i);                
                string opStr = "op_" + idxStr;
                def->addInstance(opStr, opModule);
                def->connect("self.in." + idxStr, opStr + ".in");
                def->connect(opStr + ".out", "self.out." + idxStr);
            }
            string oneConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            def->connect(oneConst + ".out", "self.ready");
            def->connect(oneConst + ".out", "self.valid");
            
        });

    /* 
     * This implementation of map is fully sequential, it will take the input in over cycles
     * equal to length of input 
     */
    Generator* mapSequential =
        aetherlinglib->newGeneratorDecl("mapSequential", aetherlinglib->getTypeGen("mapT_type"), mapXTparams);

    mapParallel->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            uint parallelism = genargs.at("parallelism")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            Type* inputElementType = opType->sel("in");
            uint elementWidth = inputElementType->getSize()

            Values hydratedType({
                    {"hydratedType", Const::make(c, inputElementType)}
                });
            Module* dehydrateInput = c->getGenerator("aetherlinglib.dehydrate")->getModule(hydratedType);
            /* this part is responsible for getting 1 input per clock */
            // serializer will choose 1 input at a time, dehydrate converts complex types to bit arrays
            // hydrate converts them back
            def->addInstance("dehydrateForSerializer", "aetherlinglib.mapN", {
                    {"numInputs", Const::make(c, numInputs)},
                    {"operator", Const::make(c, dehydrateInput)}
                });

            def->addInstance("serializer", "commonlib.seralizer", {
                    {"width", elementWidth},
                    {"rate", numInputs}
                });
            def->addInstance("readyAndValid", "coreir.and", {
                    {"width", Const::make(c, elementWidth)}
                });
            def->addInstance("hydrateForSerializer", "aetherling.hydrate", hydratedType);

            def->connect("self.in", "dehydrateForSeralizer.in");
            def->connect("dehydrateForSeralizer.out", "serializer.in");
            def->connect("serializer.out", "hydrateForSerializer.in");
            // run serializer wehn previous input is valid and next is ready
            // maybe this should always be enabled and reset when both ready and valid?
            def->connect("self.nextReady", "readyAndvalid.in0");
            def->connect("self.prevValid", "readyAndValid.in1");
            def->connect("readyAndValid.out", "seralizer.en");

            /* this part does the actual math */
            def->addInstance("op", opModule);
            def->connect("hydrateForSerializer.out", "op.in");
            def->connect("op.out", "self.out." + idxStr);

            

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
            
        });
}
