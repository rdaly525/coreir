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
    Params reduceParallelSequentialParams = Params({
            {"numInputs", c->Int()},
            {"operator", ModuleType::make(c)}
        });

    /*
     * reduceParallelPower2Inputs requires that the inputs is a power of 2
     */
    aetherlinglib->newTypeGen(
        "reduceParallelPower2Inputs_type", // name for typegen
        reduceParallelSequentialParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in0")->Arr(numInputs)},
                    {"out", opType->sel("out")},
                });
        });

    Generator* reduceParallelPower2Inputs =
        aetherlinglib->newGeneratorDecl("reduceParallelPower2Inputs", aetherlinglib->getTypeGen("reduceParallelPower2Inputs_type"), reduceParallelSequentialParams);

    reduceParallelPower2Inputs->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            ASSERT(IsPowerOfTwo(numInputs), "numInputs is not a power of 2 for reduceParallelPower2Inputs, use the reduceParallel module for this case");
            uint depth = int(ceil(log2(numInputs)));
            Module* opModule = genargs.at("operator")->get<Module*>();

            // create each layer for all dpeths other than input
            for (uint i = 0; i < depth; i++) {
                // since its a binary tree, each layer has 2^i elements
                for (uint j = 0; j < pow(2, i); j++) {
                    string opStr = getOpName(i, j);
                    def->addInstance(opStr, opModule);
                    // wire up inputs special only if first layer
                    if (i == depth - 1) {
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
        reduceParallelSequentialParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint inputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", c->Record({
                                {"data", opType->sel("in0")->Arr(inputs)},
                                {"identity", opType->sel("in0")}
                            })},
                    {"out", opType->sel("out")}
                });
        });

    Generator* reduceParallel =
        aetherlinglib->newGeneratorDecl("reduceParallel", aetherlinglib->getTypeGen("reduceParallel_type"), reduceParallelSequentialParams);

    reduceParallel->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            uint numInputsRoundedUpToPow2 = int(pow(2,ceil(log2(numInputs))));
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            uint elementWidth = opType->sel("out")->getSize();
            
            def->addInstance("reducer", "aetherlinglib.reduceParallelPower2Inputs", {
                    {"numInputs", Const::make(c, numInputsRoundedUpToPow2)},
                    {"operator", Const::make(c, opModule)}
                });

            uint i;
            for (i = 0; i < numInputs; i++) {
                string iStr = to_string(i);
                def->connect("self.in.data." + iStr, "reducer.in." + iStr);
            }
            // hook up the identity to a term if not needed as power 2 inputs
            if (i == numInputsRoundedUpToPow2) {
              def->addInstance("identityTerm", "coreir.term", {{"width", Const::make(c,elementWidth)}});
              def->connect("self.in.identity", "identityTerm.in");
            }
            else {
              // connect identity to rest of in now, all others up to power of 2
              for (; i < numInputsRoundedUpToPow2; i++) {
                  def->connect("self.in.identity", "reducer.in." + to_string(i));
              }
            }
            def->connect("reducer.out", "self.out");
        });

      aetherlinglib->newTypeGen(
        "reduceSequential_type", // name for typegen
        reduceParallelSequentialParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in0")},
                    {"out", opType->sel("out")},
                    {"valid", c->Bit()}
                });
        });

    Generator* reduceSequential =
        aetherlinglib->newGeneratorDecl("reduceSequential", aetherlinglib->getTypeGen("reduceSequential_type"), reduceParallelSequentialParams);

    reduceSequential->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            uint elementWidth = opType->sel("out")->getSize();
            Const* elementWidthConst = Const::make(c,elementWidth);

            // counter selects the input to the accumulator
            def->addInstance("counter", "commonlib.counter", {
                    {"width", elementWidthConst},
                    {"min",Const::make(c,0)},
                    {"max",Const::make(c,numInputs-1)},
                    {"inc",Const::make(c,1)}}
                );
            def->addInstance("equal", "coreir.eq",
                             {{"width", elementWidthConst}});
            def->addInstance("zero", "coreir.const",
                             {{"width", elementWidthConst}},
                             {{"value", Const::make(c, elementWidth, 0)}});
            
            def->addInstance("op", opModule);
            def->addInstance("accumulatorReg", "coreir.reg",
                             {{"width", Const::make(c, elementWidth)}});
            // on the first clock cycle, store first input, all other clock cycles, store
            // f(accumulator, nextInput)
            def->addInstance("accumulatorInputMux", "commonlib.muxn", {
                    {"width", Const::make(c, elementWidth)},
                    {"N", Const::make(c, 2)}});
            // shoudl this output be sent directly to the out?

            def->connect("self.in", "op.in0");
            def->connect("accumulatorReg.out", "op.in1");
            def->connect("op.out", "accumulatorInputMux.in.data.0");
            def->connect("self.in", "accumulatorInputMux.in.data.1");
            def->connect("accumulatorInputMux.out", "accumulatorReg.in");
            def->connect("accumulatorInputMux.out", "self.out");
            // if counter is 0 (first clock of iteration through inputs) use input 0 for accumulator
            // value. otherwise, use output of op
            def->connect("zero.out","equal.in0");
            def->connect("counter.out","equal.in1");
            def->connect("equal.out", "accumulatorInputMux.in.sel.0");
            // valid on overflow
            def->connect("counter.overflow", "self.valid");
            // force no reset on counter
            string disableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 0));
            string enableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            def->connect(disableConst + ".out.0", "counter.reset");
            def->connect(enableConst + ".out.0", "counter.en");
        });    
            
}
