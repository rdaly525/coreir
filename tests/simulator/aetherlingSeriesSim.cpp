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

        SECTION("aetherlinglib conv1D with 16 values for data, 3 values for kernel, 2 values input per clock, 16 bit width then conv1D with 16 bits for data, 2 values for kernel, 1 value input per clock") {

            convParams_t conv1Params = {16, 2, 3, 16};
            convParams_t conv2Params = {16, 2, 2, 16};

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"in", c->BitIn()->Arr(conv1Params.elementWidth)->Arr(conv1Params.inputsPerClock)},
                    {"out", c->Bit()->Arr(conv2Params.elementWidth)->Arr(conv2Params.inputsPerClock)},
                    {"valid", c->Bit()}                        
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainConv1DTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Values conv1GenArgs = {
                {"dataWidth", Const::make(c, conv1Params.dataWidth)},
                {"inputsPerClock", Const::make(c, conv1Params.inputsPerClock)},
                {"kernelWidth", Const::make(c, conv1Params.kernelWidth)},
                {"elementWidth", Const::make(c, conv1Params.elementWidth)},
            };

            Values conv2GenArgs = {
                {"dataWidth", Const::make(c, conv2Params.dataWidth)},
                {"inputsPerClock", Const::make(c, conv2Params.inputsPerClock)},
                {"kernelWidth", Const::make(c, conv2Params.kernelWidth)},
                {"elementWidth", Const::make(c, conv2Params.elementWidth)},
            };

            string conv1Name = "conv1_test";
            string conv2Name = "conv2_test";
            Instance* conv1 = def->addInstance(conv1Name, "aetherlinglib.conv1D", conv1GenArgs);
            Instance* conv2 = def->addInstance(conv2Name, "aetherlinglib.conv1D", conv2GenArgs);
            string wenModule = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            def->connect(wenModule + ".out.0", conv1Name + ".wen");
            // create different input for each element of kernel
            for (uint i = 0 ; i < conv1Params.kernelWidth; i++) {
                string constName = "constInput_conv1_" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, conv1Params.elementWidth)}},
                    {{"value", Const::make(c, conv1Params.elementWidth, i)}});

                def->connect(constName + ".out", conv1Name + ".in.kernel." + to_string(i));
            }

            for (uint i = 0 ; i < conv2Params.kernelWidth; i++) {
                string constName = "constInput_conv2_" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, conv2Params.elementWidth)}},
                    {{"value", Const::make(c, conv2Params.elementWidth, i+2)}});

                def->connect(constName + ".out", conv2Name + ".in.kernel." + to_string(i));
            }

            def->connect("self.in", conv1Name + ".in.data");
            def->connect(conv1Name + ".out", conv2Name + ".in.data");
            def->connect(conv2Name + ".out", "self.out");
            def->connect(conv1Name + ".valid", conv2Name + ".wen");
            def->connect(conv2Name + ".valid", "self.valid");

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
            for (uint clkCount = 0, numValidClks = 0; numValidClks < conv2Params.dataWidth / conv2Params.inputsPerClock ; clkCount++) {
                state.setClock("self.clk", 0, 1); // get a new rising clock edge
                // set the input
                for (uint inputIdx = 0; inputIdx < conv1Params.inputsPerClock; inputIdx++) {
                    state.setValue("self.in_" + to_string(inputIdx), BitVector(conv1Params.elementWidth,
                                                                    clkCount*conv1Params.inputsPerClock + inputIdx));
                }
                state.exeCombinational();
                // should be valid after both conv1 and 2 are valid
                // note: subtract 1 more for 0 indexing
                if (clkCount < cyclesForConvToBeValid(conv1Params) + cyclesForConvToBeValid(conv2Params) - 1) {
                    REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
                }
                else {
                    REQUIRE(state.getBitVec("self.valid") == BitVector(1, 1));
                    uint * conv1Output = new uint[conv1Params.inputsPerClock];
                    for (uint inputIdx = 0; inputIdx < conv1Params.inputsPerClock; inputIdx++) {
                        // compute the outputs of conv1
                        conv1Output[inputIdx] = 0;
                        for (uint i = 0; i < conv1Params.kernelWidth; i++) {
                            // 2 inputs per clock, by time outputing, emitting output for inputs
                            // 0,1,2 and 1,2,3 on first cycle (i inside parethenses creates each sequence
                            // of 3, i outside is for kernel element
                            conv1Output[inputIdx] += (numValidClks*conv1Params.inputsPerClock+inputIdx+i)*i;
                        }

                    }

                    uint rightOutput = 0;
                    for (uint i = 0; i < conv2Params.kernelWidth; i++) {
                        // all outputs of conv1 are multiplied by the kernel, then summed up
                        rightOutput += conv1Output[i]*(i+2);
                    }
                    REQUIRE(state.getBitVec("self.out_0") ==
                            BitVector(conv1Params.elementWidth, rightOutput));
                    delete [] conv1Output;

                    numValidClks++;
                }
                state.exeSequential();
            }
        }
        deleteContext(c);
    }
}
