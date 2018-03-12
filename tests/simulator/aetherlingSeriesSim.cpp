//#define CATCH_CONFIG_MAIN

#include "catch.hpp"

#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"
#include "coreir/simulator/interpreter.h"
#include "coreir/libs/commonlib.h"
#include "coreir/libs/aetherlinglib.h"

#include <iostream>
#include <math.h>

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

typedef struct convParams {
    uint dataWidth;
    uint inputsPerClock;
    uint kernelWidth;
    uint elementWidth;
} convParams_t;
        
namespace CoreIR {

    uint cyclesForConvToBeValid(convParams_t cp) {
        return (cp.kernelWidth + cp.inputsPerClock - 1) / cp.inputsPerClock;
    }


    TEST_CASE("Simulate multiple convolutions from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        SECTION("3 conv1D with 16 values for data, 3 values for kernel, 2 values input per clock, 16 bit width then conv1D with 16 bits for data, 2 values for kernel, 1 value input per clock") {

            convParams_t convParams = {16, 2, 3, 16};

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"in", c->BitIn()->Arr(convParams.elementWidth)->Arr(convParams.inputsPerClock)},
                    {"out", c->Bit()->Arr(convParams.elementWidth)->Arr(convParams.dataWidth)},
                    {"valid", c->Bit()}                        
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainConv1DTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Values convGenArgs = {
                {"dataWidth", Const::make(c, convParams.dataWidth)},
                {"inputsPerClock", Const::make(c, convParams.inputsPerClock)},
                {"kernelWidth", Const::make(c, convParams.kernelWidth)},
                {"elementWidth", Const::make(c, convParams.elementWidth)},
            };

            string conv1Name = "conv1_test";
            string conv2Name = "conv2_test";
            Instance* conv1 = def->addInstance(conv1Name, "aetherlinglib.conv1D", convGenArgs);
            Instance* conv2 = def->addInstance(conv2Name, "aetherlinglib.conv1D", convGenArgs);
            
            Module* add = c->getGenerator("coreir.add")->
                getModule({{"width", Const::make(c, convParams.elementWidth)}});
            Instance* mapAdders = def->addInstance("mapAdders", "aetherlinglib.mapParallel", {
                    {"numInputs", Const::make(c, convParams.inputsPerClock)},
                    {"operator", Const::make(c, add)}
                });

            ArrayType* mapAddersOutType = dyn_cast<ArrayType>(mapAdders->getType()->sel("out"));
            uint streamifyPairedLength = convParams.dataWidth/convParams.inputsPerClock;

            def->addInstance("pairCollector", "aetherlinglib.arrayify", {
                    {"elementType", Const::make(c, mapAddersOutType)},
                    {"arrayLength", Const::make(c, streamifyPairedLength)}
                });

            def->addInstance("pairToFullArrayFlatten", "aetherlinglib.flatten", {
                    {"inputType", Const::make(c, c->In(mapAddersOutType->Arr(streamifyPairedLength)))},
                    {"singleElementOutputType", Const::make(c, mapAddersOutType->getElemType())}
                });            
            
            // create different input for each element of kernel
            for (uint i = 0 ; i < convParams.kernelWidth; i++) {
                string constName = "constInput_test_" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, convParams.elementWidth)}},
                    {{"value", Const::make(c, convParams.elementWidth, i)}});

                def->connect(constName + ".out", conv1Name + ".in.kernel." + to_string(i));
                def->connect(constName + ".out", conv2Name + ".in.kernel." + to_string(i));
            }

            def->connect("self.in", conv1Name + ".in.data");
            def->connect("self.in", conv2Name + ".in.data");
            def->connect(conv1Name + ".out", "mapAdders.in0");
            def->connect(conv2Name + ".out", "mapAdders.in1");
            def->connect("mapAdders.out", "pairCollector.in");
            def->connect("pairCollector.out", "pairToFullArrayFlatten.in");
            def->connect("pairToFullArrayFlatten.out", "self.out");

            // handle enable/reset beauracracy 
            string wenModule = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            string disableModule = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 0));
            def->addInstance("bothConvsValid", "coreir.and",
                             {{"width", Const::make(c, 1)}});
            def->connect(wenModule + ".out.0", conv1Name + ".wen");
            def->connect(wenModule + ".out.0", conv2Name + ".wen");
            def->connect(conv1Name + ".valid", "bothConvsValid.in0.0");
            def->connect(conv2Name + ".valid", "bothConvsValid.in1.0");
            def->connect("bothConvsValid.out.0", "pairCollector.en");
            def->connect(disableModule + ".out.0", "pairCollector.reset");
            def->connect("pairCollector.valid", "self.valid");

            mainModule->setDef(def);
            mainModule->print();
            conv1->getModuleRef()->print();

            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();
                                    
            SimulatorState state(mainModule);
            // pass in increasing numbers each clock cycle, should get 1*2*3 times that number
            // once valid is right, should get items out in same order sent in           
            for (uint clkCount = 0, numValidClks = 0; numValidClks < 1 ; clkCount++) {
                state.setClock("self.clk", 0, 1); // get a new rising clock edge
                // set the input
                for (uint inputIdx = 0; inputIdx < convParams.inputsPerClock; inputIdx++) {
                    state.setValue("self.in_" + to_string(inputIdx), BitVector(convParams.elementWidth,
                                                                    clkCount*convParams.inputsPerClock + inputIdx));
                }
                state.exeCombinational();
                if(state.getBitVec("self.valid") == BitVector(1, 1)) {
                    uint * conv1Output = new uint[convParams.dataWidth];
                    for (uint inputIdx = 0; inputIdx < convParams.dataWidth; inputIdx++) {
                        // compute the outputs of conv1
                        uint rightOutput = 0;
                        for (uint i = 0; i < convParams.kernelWidth; i++) {
                            // 2 inputs per clock, by time outputing, emitting output for inputs
                            // 0,1,2 and 1,2,3 on first cycle (i inside parethenses creates each sequence
                            // of 3, i outside is for kernel element
                            rightOutput += (inputIdx+i)*i;
                        }
                        REQUIRE(state.getBitVec("self.out_" + to_string(inputIdx)) ==
                            BitVector(convParams.elementWidth, 2*rightOutput));
                    }
                    delete [] conv1Output;

                    numValidClks++;
                }
                state.exeSequential();
            }
        }
        deleteContext(c);
    }
}
