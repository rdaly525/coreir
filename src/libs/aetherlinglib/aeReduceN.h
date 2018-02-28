#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <math.h>

using namespace std;
using namespace CoreIR;

string getOpName(int layer, int idxInLayer) {
    return "op_" + to_string(layer) + "_" + to_string(idxInLayer);
}

// https://stackoverflow.com/a/600306
bool IsPowerOfTwo(uint x)
{
    return (x != 0) && ((x & (x - 1)) == 0);
}

void Aetherling_createReduceGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * numInputs - the number of eleemnts to reduce 
     * operator - the operator to parallelize. Note that it must have two inputs known as "in0" and "in1" and 
     * one output known as "out"
     */
    Params reduceParallelSerialParams = Params({
            {"numInputs", c->Int()},
            {"operator", ModuleType::make(c)}
        });

    /*
     * reduceParallelPower2Inputs requires that the inputs is a power of 2
     */
    aetherlinglib->newTypeGen(
        "reduceParallelPower2Inputs_type", // name for typegen
        reduceParallelSerialParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in0")->Arr(numInputs)},
                    {"out", opType->sel("out")},
                    {"ready", c->Bit()},
                    {"valid", c->Bit()}
                });
        });

    Generator* reduceParallelPower2Inputs =
        aetherlinglib->newGeneratorDecl("reduceParallelPower2Inputs", aetherlinglib->getTypeGen("reduceParallelPower2Inputs_type"), reduceParallelParams);

    reduceParallelPower2Inputs->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            ASSERT(IsPowerOfTwo(inputs), "numInputs is not a power of 2 for reduceParallelPower2Inputs, use the reduceParallel module for this case");
            uint depth = int(ceil(log2(numInputs)));
            Module* opModule = genargs.at("operator")->get<Module*>();
            assert(numLayers>0);

            // create each layer for all dpeths other than input
            for (uint i = 0; i < depth; i++) {
                // since its a binary tree, each layer has 2^i elements
                for (uint j = 0; j < pow(2, i); j++) {
                    string opStr = getOpName(i, j);
                    def->addInstance(opStr, opModule);
                    // wire up inputs special only if first layer
                    if (i == numLayers - 1) {
                        def->connect("self.in." + to_string(j*2), opStr + ".in0");
                        def->connect("self.in." + to_string(j*2+1), opStr + ".in1");
                    }
                    // wire output special only if last layer
                    if (i == 0) {
                        def->connect(opStr + ".out", "self.out");
                    }
                    else {
                        def->connect(opStr + ".out", getOpName(i-1, j/2) + ".in" + to_string(j % 2));
                    }
                }
            }
            // always ready and valid
            string enableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            def->connect(enableConst + ".out.0", "self.ready");
            def->connect(enableConst + ".out.0", "self.valid");
        });

    /*
     * This reducer allows for non-powers of 2 inputs, requires an identity for operator so that can wire
     * up all irrelevant inputs to it.
     * numInputs - the total number of inputs to this module
     * operator - the operator to parallelize. Note that it must have two inputs known as "in0" and "in1" and 
     * one output known as "out"
     */
    aetherlinglib->newTypeGen(
        "reduceParallel_type", // name for typegen
        reduceParallelSerialParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint inputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", c->Record({
                                {"data", opType->sel("in0")->Arr(inputs)},
                                {"identity", opType->sel("in0")}
                            })},
                    {"out", opType->sel("out")},
                    {"ready", c->Bit()},
                    {"valid", c->Bit()}
                });
        });

    Generator* reduceParallel =
        aetherlinglib->newGeneratorDecl("reduceParallel", aetherlinglib->getTypeGen("reduceParallel_type"), reduceParallelParams);

    reduceParallel->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            uint numInputsRoundedUpToPow2 = int(pow(2,ceil(log2(numInputs))));
            Module* opModule = genargs.at("operator")->get<Module*>();
            
            def->addInstance("reducer", "aetherlinglib.reduceParallelPower2Inputs", {
                    {"numInputs", Const::make(c, numInputsRoundedUpToPow2)},
                    {"operator", Const::make(c, opModule)}
                });

            uint i;
            for (i = 0; i < numInputs; i++) {
                string iStr = to_string(i);
                def->connect("self.in.data." + iStr, "reducer.in." + iStr);
            }
            // connect identity to rest of in now, all others up to power of 2
            for (; i < numInputsRoundedUpToPow2; i++) {
                def->connect("self.in.identity", "reducer.in." + to_string(i));
            }
            def->connect("reducer.out", "self.out");
            def->connect("reducer.ready", "self.ready");
            def->connect("reducer.valid", "self.valid");
        });

    aetherlinglib->newTypeGen(
        "reduceSequential_type", // name for typegen
        reduceParallelSequentialParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint inputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in0")->Arr(numInputs)},
                    {"out", opType->sel("out")},
                    {"ready", c->Bit()},
                    {"valid", c->Bit()}
                });
        });

    Generator* reduceSequential =
        aetherlinglib->newGeneratorDecl("reduceSequential", aetherlinglib->getTypeGen("reduceSequential_type"), reduceSequentialParallelParams);


    reduceSequential->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            uint elementWidth = opType->sel("out")->getSize();
            
            Values streamifyParams({
                    {"elementType", Const::make(c, opType->sel("in0"))},
                    {"arrayLength", Const::make(c, numInputs)} 
                });

            def->addInstance("streamify", "aetherlinglib.streamify", streamifyParams);
            def->addInstance("op", opModule);
            def->addInstance("accumulatorReg", "coreir.reg",
                             {{"width", Const::make(c, elementWidth)}});
            // on the first clock cycle, store first input, all other clock cycles, store
            // f(accumulator, nextInput)
            def->addInstance("accumulatorInputMux", "commonlib.muxn", {
                    {"width", Const::make(c, elementWidth)},
                    {"N", Const::make(c, 2)}});

            def->connect("self.in", "streamify.in");
            def->connect("streamify.out", "op.in0");
            def->connect("accumlatorReg.out", "op.in1");
            def->connect("op.out", "accumulatorInputmux.in.data.0");
            def->connect("self.in.0", "accumulatorInputMux.in.data.1");
            def->connect("accumulatorInputMux.out", "accumulatorReg.in");
            // if ready is 1 (first clock of iteration through inputs) use in 0, for accumulator
            // value. otherwise, use output of op
            def->connect("streamify.ready", "accumulatorInputMux.sel.0");
        });

      aetherlinglib->newTypeGen(
        "reduceSequential_type", // name for typegen
        reduceParallelSequentialParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint inputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in0")->Arr(numInputs)},
                    {"out", opType->sel("out")},
                    {"ready", c->Bit()},
                    {"valid", c->Bit()}
                });
        });

    Generator* reduceSequentialMultipleClocks =
        aetherlinglib->newGeneratorDecl("reduceSequential", aetherlinglib->getTypeGen("reduceSequential_type"), reduceSequentialParallelParams);


    reduceSequential->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            uint elementWidth = opType->sel("out")->getSize();
            
            Values streamifyParams({
                    {"elementType", Const::make(c, opType->sel("in0"))},
                    {"arrayLength", Const::make(c, numInputs)} 
                });

            def->addInstance("streamify", "aetherlinglib.streamify", streamifyParams);
            def->addInstance("op", opModule);
            def->addInstance("accumulatorReg", "coreir.reg",
                             {{"width", Const::make(c, elementWidth)}});
            // on the first clock cycle, store first input, all other clock cycles, store
            // f(accumulator, nextInput)
            def->addInstance("accumulatorInputMux", "commonlib.muxn", {
                    {"width", Const::make(c, elementWidth)},
                    {"N", Const::make(c, 2)}});

            def->connect("self.in", "streamify.in");
            def->connect("streamify.out", "op.in0");
            def->connect("accumlatorReg.out", "op.in1");
            def->connect("op.out", "accumulatorInputmux.in.data.0");
            def->connect("self.in.0", "accumulatorInputMux.in.data.1");
            def->connect("accumulatorInputMux.out", "accumulatorReg.in");
            // if ready is 1 (first clock of iteration through inputs) use in 0, for accumulator
            // value. otherwise, use output of op
            def->connect("streamify.ready", "accumulatorInputMux.sel.0");
        });    
            
}
