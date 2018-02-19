#include "coreir.h"
#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <execinfo.h>
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>



using namespace std;
using namespace CoreIR;

void handler(int sig) {
  void *array[10];
  size_t size;

  // get void*'s for all entries on the stack
  size = backtrace(array, 10);

  // print out all the frames to stderr
  fprintf(stderr, "Error: signal %d:\n", sig);
  backtrace_symbols_fd(array, size, STDERR_FILENO);
  exit(1);
}

int main() {
    signal(SIGSEGV, handler);   // install our handler
    Context* c = newContext();
    CoreIRLoadLibrary_commonlib(c);
    CoreIRLoadLibrary_aetherlinglib(c);

    uint parallelInputs = 4;
    uint notPow2ParallelInputs = 3;
    uint width = 16;

    Type* inFlattenType = c->BitIn()->Arr(2)->Arr(2)->Arr(2);
    Type* outFlattenType = c->Bit()->Arr(2);
    
    //Type of module 
    Type* oneInManyOutGenType = c->Record({
            {"in",c->BitIn()->Arr(width)->Arr(parallelInputs)},
            {"inFlatten", inFlattenType},
            {"outMap",c->Bit()->Arr(width)->Arr(parallelInputs)},
            {"outReduce",c->Bit()->Arr(width)},
            {"outConv1D", c->Bit()->Arr(width)},
            {"outFlatten", outFlattenType->Arr(4)},
            {"validConv1D", c->Bit()}
        });
    Module* testModule = c->getGlobal()->newModuleDecl("testModule",oneInManyOutGenType);
    ModuleDef* testDef = testModule->newModuleDef();

    // creating map for testing
    
    //Type of module
    Type* twoInZippedOneOutGenType = c->Record({
            {"in", c->Record({
                        {"el0", c->BitIn()->Arr(width)},
                        {"el1", c->BitIn()->Arr(width)}
                    })},
            {"out",c->Bit()->Arr(width)}
        });

    

    /* creating the mulBy2 that the mapN will parallelize */
    Module* mul2Inputs = c->getGlobal()->newModuleDecl("mul2Inputs", twoInZippedOneOutGenType);
    ModuleDef* mul2InputsDef = mul2Inputs->newModuleDef();
        

    string constModule = Aetherling_addCoreIRConstantModule(c, testDef, width, Const::make(c, width, 4));
    mul2InputsDef->addInstance("mul", "coreir.mul", {{"width", Const::make(c, width)}});
    mul2InputsDef->connect("self.in.el0", "mul.in0");
    mul2InputsDef->connect("self.in.el1", "mul.in1");
    mul2InputsDef->connect("mul.out", "self.out");
    mul2Inputs->setDef(mul2InputsDef);

    Values zip2Params({
            {"numInputs", Const::make(c, parallelInputs)},
            {"input0Type", Const::make(c, c->BitIn()->Arr(width))},
            {"input1Type", Const::make(c, c->BitIn()->Arr(width))}
        });
    
    Values mapNParams({
            {"parallelOperators", Const::make(c, parallelInputs)},
            {"operator", Const::make(c, mul2Inputs)}
        });

    // ignoring last argumen to addIstance as no module parameters
    testDef->addInstance("zip2", "aetherlinglib.zip2", zip2Params);
    testDef->addInstance("mapMul", "aetherlinglib.mapN", mapNParams);

    // creating reduce for testing
    Module* add = c->getGenerator("coreir.add")->getModule({{"width", Const::make(c, width)}});

    Values reduceNParams({
            {"numLayers", Const::make(c, int(log2(parallelInputs)))},
            {"operator", Const::make(c, add)}
        });

    testDef->addInstance("reduceAdd", "aetherlinglib.reduceN", reduceNParams);

    // creating convolution for testing
    uint dataWidth = notPow2ParallelInputs*4;
    testDef->addInstance("conv1D", "aetherlinglib.conv1D", {
            {"dataWidth", Const::make(c, dataWidth)},
            {"inputPerClockWidth", Const::make(c, 1)},
            {"kernelWidth", Const::make(c, notPow2ParallelInputs)},
            {"elementWidth", Const::make(c, width)}
        });


    // creating flatten for testing
    testDef->addInstance("flattenTest", "aetherlinglib.flattenN", {
            {"inputType", Const::make(c, inFlattenType)},
            {"singleElementOutputType", Const::make(c, outFlattenType)}
        });

    // wiring up the flatten
    testDef->connect("self.inFlatten", "flattenTest.in");
    testDef->connect("flattenTest.out", "self.outFlatten");

    // wiring up the kernel and the data inputs, everythign is same as justing if wiring works
    for (uint i = 0; i < notPow2ParallelInputs; i++) {
        testDef->connect(constModule + ".out", "conv1D.in.kernel." + to_string(i));
    }

    testDef->connect(constModule + ".out", "conv1D.in.data.0");
    
    testDef->connect("conv1D.out", "self.outConv1D");
    testDef->connect("conv1D.valid", "self.validConv1D");
    string wenModule = Aetherling_addCoreIRConstantModule(c, testDef, 1, Const::make(c, 1, 1));
    testDef->connect(wenModule + ".out.0", "conv1D.wen");


    // wiring up zippped input to mul
    testDef->connect("self.in","zip2.in0");
    for (uint i = 0; i <parallelInputs; i++) {
        testDef->connect(constModule + ".out", "zip2.in1." + to_string(i));
    }
    testDef->connect("zip2.out", "mapMul.in");
    testDef->connect("mapMul.out","self.outMap");

    // wiring up reduce
    testDef->connect("self.in", "reduceAdd.in");
    testDef->connect("reduceAdd.out", "self.outReduce");

    testModule->setDef(testDef);
    testModule->print();
    c->runPasses({"rungenerators", "verifyconnectivity"});
  
    testModule->print();
    cout << testModule->toString() << endl;
  
    deleteContext(c);
    return 0;
}
