#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>

using namespace std;
using namespace CoreIR;

void Aetherling_createMapGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * This type is for all maps, from fully sequential to fully parallel
     * parallelOperatrs - how many operators to have in parallel
     * operator - the operator to parallelize. Note that it must have one input known as "in" and 
     * one output known as "out"
     */
    Params mapSeqParParams = Params({
            {"numInputs", c->Int()},
            {"operator", ModuleType::make(c)},
        });

    /*
     * All versions of map take the entire input in at once and emit a valid signal when the output is correct.
     * This is done to keep a consistent type interface so compiler transformations are easier.
     */
    aetherlinglib->newTypeGen(
        "mapSeqPar_type", // name for typegen
        mapSeqParParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in")->Arr(numInputs)},
                    {"out", opType->sel("out")->Arr(numInputs)},
                    {"ready", c->Bit()},
                    {"valid", c->Bit()}
                });
        });

    Generator* mapParallel =
        aetherlinglib->newGeneratorDecl("mapParallel", aetherlinglib->getTypeGen("mapSeqPar_type"), mapSeqParParams);

    mapParallel->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();

            // now create each op and wire the inputs and outputs to it
            for (uint i = 0; i < numInputs; i++) {
                string idxStr = to_string(i);                
                string opStr = "op_" + idxStr;
                def->addInstance(opStr, opModule);
                def->connect("self.in." + idxStr, opStr + ".in");
                def->connect(opStr + ".out", "self.out." + idxStr);
            }
            string oneConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            def->connect(oneConst + ".out.0", "self.ready");
            def->connect(oneConst + ".out.0", "self.valid");
            
        });

    /* 
     * This implementation of map is fully sequential, it will take the input in over cycles
     * equal to length of input 
     */
    Generator* mapSequential =
        aetherlinglib->newGeneratorDecl("mapSequential", aetherlinglib->getTypeGen("mapSeqPar_type"), mapSeqParParams);

    mapSequential->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            Type* inputElementType = opType->sel("in");

            Values streamifyArrayifyParams({
                    {"elementType", Const::make(c, inputElementType)},
                    {"arrayLength", Const::make(c, numInputs)}
                });

            def->addInstance("streamify", "aetherlinglib.streamify", streamifyArrayifyParams);
            def->addInstance("op", opModule);
            def->addInstance("arrayify", "aetherlinglib.arrayify", streamifyArrayifyParams);

            // do the work
            def->connect("self.in", "streamify.in");
            def->connect("streamify.out", "op.in");
            def->connect("op.out", "arrayify.in");
            def->connect("arrayify.out", "self.out");

            // handle the overhead
            string enableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            string disableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 0));
            def->connect(enableConst + ".out.0", "streamify.en");
            def->connect(enableConst + ".out.0", "arrayify.en");
            def->connect("streamify.ready", "self.ready");
            def->connect("arrayify.valid", "self.valid");
            def->connect(disableConst + ".out.0", "streamify.reset");
            def->connect(disableConst + ".out.0", "arrayify.reset");
        });
}
