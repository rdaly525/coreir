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
            string oneConst;
            // if op has ready or valid, wire those up to this map's ready and valid
            // create a one output if this map needs to drive either its own ready or valid
            cout << "as" << endl;
            bool hasReady = opModule->getType()->canSel("ready");
            bool hasValid = opModule->getType()->canSel("valid");
            cout << "a" << endl;
            if (!hasReady || !hasValid) {
                oneConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            }
            // all ops should be same, so can take ready and valid from first op
            if (hasReady) {
                def->connect("op_0.ready", "self.ready");
            }
            else {
                def->connect(oneConst + ".out.0", "self.ready");
            }
            cout << "b" << endl;
            if (hasValid) {
                def->connect("op_0.valid", "self.valid");
            }
            else {
                def->connect(oneConst + ".out.0", "self.valid");
            }
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
            Type* outputElementType = opType->sel("out");

            Values streamifyParams({
                    {"elementType", Const::make(c, inputElementType)},
                    {"arrayLength", Const::make(c, numInputs)}
                });
            Values arrayifyParams({
                    {"elementType", Const::make(c, outputElementType)},
                    {"arrayLength", Const::make(c, numInputs)}
                });

            def->addInstance("streamify", "aetherlinglib.streamify", streamifyParams);
            def->addInstance("op", opModule);
            def->addInstance("arrayify", "aetherlinglib.arrayify", arrayifyParams);

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
