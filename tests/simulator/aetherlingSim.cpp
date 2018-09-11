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

namespace CoreIR {

    TEST_CASE("Simulate map from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        uint width = 16;
        uint numInputs = 4;
        uint constInput = 3;

        CoreIRLoadLibrary_commonlib(c);
        CoreIRLoadLibrary_aetherlinglib(c);
        
        Type* twoInZippedOneOutGenType = c->Record({
                {"in",c->Record({
                            {"el0", c->BitIn()->Arr(width)},
                            {"el1", c->BitIn()->Arr(width)}
                        })},
                {"out",c->Bit()->Arr(width)}
            });

        /* creating the mulBy2 that the mapParallel will parallelize */
        Module* mul2Inputs = c->getGlobal()->newModuleDecl("mul2Inputs", twoInZippedOneOutGenType);
        ModuleDef* mul2InputsDef = mul2Inputs->newModuleDef();        

        mul2InputsDef->addInstance("mul", "coreir.mul", {{"width", Const::make(c, width)}});
        mul2InputsDef->connect("self.in.el0", "mul.in0");
        mul2InputsDef->connect("self.in.el1", "mul.in1");
        mul2InputsDef->connect("mul.out", "self.out");
        mul2Inputs->setDef(mul2InputsDef);

        Values zip2Params({
                {"numInputs", Const::make(c, numInputs)},
                {"input0Type", Const::make(c, c->BitIn()->Arr(width))},
                {"input1Type", Const::make(c, c->BitIn()->Arr(width))}
            });
    
        Values mapParams({
                {"numInputs", Const::make(c, numInputs)},
                {"operator", Const::make(c, mul2Inputs)}
            });

        SECTION("aetherlinglib mapParallel with 4 mul, 3 as constant, 16 bit width") {
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Bit()->Arr(width)->Arr(numInputs)}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainMapParallelMulTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            def->addInstance("zip2", "aetherlinglib.zip2", zip2Params);
            string mapParallelName = "map" + to_string(numInputs);
            Instance* mapParallel_mul = def->addInstance(mapParallelName, "aetherlinglib.mapParallel", mapParams);
            // here we are wiring up a constant value and an iterated one to each input of the zip before
            // it goes into the map
            string notIteratedConstModule = Aetherling_addCoreIRConstantModule(c, def, width, Const::make(c, width, constInput));

            for (uint i = 0 ; i < numInputs; i++) {
                string constName = "constInput" + to_string(i);
                def->connect(notIteratedConstModule + ".out", "zip2.in0." + to_string(i));
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, width)}},
                    {{"value", Const::make(c, width, i)}});

                def->connect(constName + ".out",  "zip2.in1." + to_string(i));
            }

            def->connect("zip2.out", mapParallelName + ".in");
            def->connect(mapParallelName + ".out", "self.out");
            
            mainModule->setDef(def);
            mapParallel_mul->getModuleRef()->print();
            c->runPasses({"rungenerators", "verifyconnectivity", "flatten", "flattentypes", "deletedeadinstances"});
            mainModule->print();

            SimulatorState state(mainModule);
            state.execute();
            
            for (uint i = 0; i < numInputs; i++) {
                REQUIRE(state.getBitVec("self.out_" + to_string(i)) == BitVector(width, i*constInput));
            }
                    
        }

        SECTION("aetherlinglib mapSequential with 4 mul, 3 as constant, 16 bit width") {
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Bit()->Arr(width)->Arr(numInputs)},
                    {"ready", c->Bit()},
                    {"valid", c->Bit()}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainMapSequentialMulTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();


            def->addInstance("zip2", "aetherlinglib.zip2", zip2Params);
            string mapSeqName = "map" + to_string(numInputs);
            Instance* mapSeq_mul = def->addInstance(mapSeqName, "aetherlinglib.mapSequential", mapParams);

            // here we are wiring up a constant value and an iterated one to each input of the zip before
            // it goes into the map
            string notIteratedConstModule = Aetherling_addCoreIRConstantModule(c, def, width, Const::make(c, width, constInput));

            for (uint i = 0 ; i < numInputs; i++) {
                string constName = "constInput" + to_string(i);
                def->connect(notIteratedConstModule + ".out", "zip2.in0." + to_string(i));
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, width)}},
                    {{"value", Const::make(c, width, i)}});

                def->connect(constName + ".out",  "zip2.in1." + to_string(i));
            }

            def->connect("zip2.out", mapSeqName + ".in");
            def->connect(mapSeqName + ".out", "self.out");
            def->connect(mapSeqName + ".ready", "self.ready");
            def->connect(mapSeqName + ".valid", "self.valid");
            
            
            mainModule->setDef(def);
            mapSeq_mul->getModuleRef()->print();
            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();

            SimulatorState state(mainModule);
            state.setClock("self.clk", 0, 1);
            // on first clock, ready should be asserted, then deasserted for rest until processed all input
            // from start until all inputs have gone through, valid should be deasserted
            for (uint i = 0; i < numInputs - 1; i++) {
                state.exeCombinational();
                REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
                REQUIRE(state.getBitVec("self.ready") == BitVector(1, i % numInputs == 0 ? 1 : 0));
                state.exeSequential();
            }
            state.exeCombinational();
            REQUIRE(state.getBitVec("self.ready") == BitVector(1, 0));
            REQUIRE(state.getBitVec("self.valid") == BitVector(1, 1));
            for (uint i = 0; i < numInputs; i++) {
                REQUIRE(state.getBitVec("self.out_" + to_string(i)) == BitVector(width, i*constInput));
            }
            state.exeSequential();
            state.exeCombinational();
            REQUIRE(state.getBitVec("self.ready") == BitVector(1, 1));
            REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
        }

        deleteContext(c);
    }

    TEST_CASE("Simulate reduce from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        uint width = 16;
        uint numInputs4 = 4;
        uint numInputs9 = 4;
        uint constInput = 3;

        CoreIRLoadLibrary_commonlib(c);
        CoreIRLoadLibrary_aetherlinglib(c);
        
        Module* add = c->getGenerator("coreir.add")->getModule({{"width", Const::make(c, width)}});
        add->print();

        Values reduce4ModArgs = {
            {"numInputs", Const::make(c, numInputs4)},
            {"operator", Const::make(c, add)}
        };

        Values reduce9ModArgs = {
          {"numInputs", Const::make(c, numInputs9)},
          {"operator", Const::make(c, add)}
        };
            
        SECTION("aetherlinglib reduceParallel with 4 inputs, coreir.add as op, 16 bit width") {
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Bit()->Arr(width)}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainReduce4ParallelTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();
            
            string reduceParallelName = "reduce" + to_string(numInputs4);
            Instance* reduceParallel_add = def->addInstance(reduceParallelName, "aetherlinglib.reduceParallel", reduce4ModArgs);
            string addIdentityConst = Aetherling_addCoreIRConstantModule(c, def, width, Const::make(c, width, 0));

            def->connect(addIdentityConst + ".out", reduceParallelName + ".in.identity");
            // create different input for each operator
            uint rightOutput = 0;
            for (uint i = 0 ; i < numInputs4; i++) {
                string constName = "constInput" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, width)}},
                    {{"value", Const::make(c, width, i)}});

                def->connect(constName + ".out", reduceParallelName + ".in.data." + to_string(i));
                rightOutput += i;
            }

            def->connect(reduceParallelName + ".out", "self.out");
            mainModule->setDef(def);
            mainModule->print();
            reduceParallel_add->getModuleRef()->print();
            c->runPasses({"rungenerators", "verifyconnectivity-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();
                                    
            SimulatorState state(mainModule);
            state.exeCombinational();

            REQUIRE(state.getBitVec("self.out") == BitVector(width, rightOutput));
        }

        SECTION("aetherlinglib reduceParallel with 9 inputs, coreir.add as op, 16 bit width") {
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Bit()->Arr(width)}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainReduceParallel9Test", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();
            
            string reduceParallelName = "reduce" + to_string(numInputs9);
            Instance* reduceParallel_add = def->addInstance(reduceParallelName, "aetherlinglib.reduceParallel", reduce9ModArgs);
            string addIdentityConst = Aetherling_addCoreIRConstantModule(c, def, width, Const::make(c, width, 0));

            def->connect(addIdentityConst + ".out", reduceParallelName + ".in.identity");
            // create different input for each operator
            uint rightOutput = 0;
            for (uint i = 0 ; i < numInputs9; i++) {
                string constName = "constInput" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, width)}},
                    {{"value", Const::make(c, width, i)}});

                def->connect(constName + ".out", reduceParallelName + ".in.data." + to_string(i));
                rightOutput += i;
            }

            def->connect(reduceParallelName + ".out", "self.out");
            mainModule->setDef(def);
            mainModule->print();
            reduceParallel_add->getModuleRef()->print();
            c->runPasses({"rungenerators", "verifyconnectivity-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();
                                    
            SimulatorState state(mainModule);
            state.exeCombinational();

            REQUIRE(state.getBitVec("self.out") == BitVector(width, rightOutput));
        }

        SECTION("aetherlinglib reduceSequential with 4 inputs, coreir.add as op, 16 bit width") {
            Type* mainModuleType = c->Record({
                    {"in", c->BitIn()->Arr(width)},
                    {"out", c->Bit()->Arr(width)},
                    {"valid", c->Bit()}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainReduceSequentialTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();
            
            string reduceSequentialName = "reduce" + to_string(numInputs4);
            Instance* reduceSequential_add = def->addInstance(reduceSequentialName, "aetherlinglib.reduceSequential", reduce4ModArgs);
            def->connect("self.in", reduceSequentialName + ".in");
            def->connect(reduceSequentialName + ".out", "self.out");
            def->connect(reduceSequentialName + ".valid", "self.valid");
            
            mainModule->setDef(def);
            mainModule->print();
            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();
                                 
            SimulatorState state(mainModule);
            state.setClock("self.clk", 0, 1);
            uint rightOutput = 0;
            // on first clock, ready should be asserted, then deasserted for rest until processed all input
            // from start until all inputs have gone through, valid should be deasserted
            uint i;
            for (i = 0; i < numInputs4 - 1; i++) {
                state.setValue("self.in", BitVector(width, i));
                rightOutput += i;
                state.exeCombinational();
                REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
                state.exeSequential();
            }
            state.setValue("self.in", BitVector(width, i));
            rightOutput += i;
            state.exeCombinational();
            REQUIRE(state.getBitVec("self.valid") == BitVector(1, 1));
            REQUIRE(state.getBitVec("self.out") == BitVector(width, rightOutput));
            state.exeSequential();
            state.exeCombinational();
            // ensure that on first cycle of next iteration, outputing right thing
            REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
            REQUIRE(state.getBitVec("self.out") == BitVector(width, i));
        }
        deleteContext(c);
    }

    TEST_CASE("Simulate convolution from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        SECTION("aetherlinglib conv1D with 9 values for data, 3 values for kernel, 1 value input per clock, 16 bit width") {
            uint dataWidth = 9;
            uint inputsPerClock = 1;
            uint kernelWidth = 3;
            uint elementWidth = 16;

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"in", c->BitIn()->Arr(elementWidth)->Arr(inputsPerClock)},
                    {"out", c->Bit()->Arr(elementWidth)->Arr(inputsPerClock)},
                    {"valid", c->Bit()}                        
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainConv1DTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Values conv1DGenArgs = {
                {"dataWidth", Const::make(c, dataWidth)},
                {"inputsPerClock", Const::make(c, inputsPerClock)},
                {"kernelWidth", Const::make(c, kernelWidth)},
                {"elementWidth", Const::make(c, elementWidth)},
            };

            string conv1DName = "conv1D_test";
            Instance* conv1D = def->addInstance(conv1DName, "aetherlinglib.conv1D", conv1DGenArgs);
            string wenModule = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            def->connect(wenModule + ".out.0", conv1DName + ".wen");
            // create different input for each element of kernel
            for (uint i = 0 ; i < kernelWidth; i++) {
                string constName = "constInput" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, elementWidth)}},
                    {{"value", Const::make(c, elementWidth, i)}});

                def->connect(constName + ".out", conv1DName + ".in.kernel." + to_string(i));
            }

            def->connect("self.in", conv1DName + ".in.data");
            def->connect(conv1DName + ".out", "self.out");
            def->connect(conv1DName + ".valid", "self.valid");

            mainModule->setDef(def);
            mainModule->print();
            conv1D->getModuleRef()->print();
            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();
                                    
            SimulatorState state(mainModule);
            // pass in increasing numbers each clock cycle, should get 1*2*3 times that number
            // once valid is right, should get items out in same order sent in           
            for (uint clkCount = 0, numValidClks = 0; numValidClks < dataWidth ; clkCount++) {
                state.setClock("self.clk", 0, 1); // get a new rising clock edge
                // set the input
                state.setValue("self.in_0", BitVector(elementWidth, clkCount));
                state.exeCombinational();

                // should be valid starting on cycle (kernelWidth + inputsPerClock - 1) / inputsPerClock
                // note: subtract 1 more for 0 indexing
                if (clkCount < (kernelWidth + inputsPerClock - 1) / inputsPerClock - 1) {
                    REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
                }
                else {
                    REQUIRE(state.getBitVec("self.valid") == BitVector(1, 1));

                    // now check that the n, n+1, ..., n+(kernelWidth-1) inputs are used to produce output
                    // on nth clock cycle of valid
                    uint rightOutput = 0;
                    for (uint i = 0; i < kernelWidth; i++) {
                        rightOutput += (numValidClks+i)*i;
                    }
                    REQUIRE(state.getBitVec("self.out_0") == BitVector(elementWidth, rightOutput));
                    numValidClks++;
                }
                state.exeSequential();
            }
        }

         SECTION("aetherlinglib conv1D with 16 values for data, 3 values for kernel, 2 values input per clock, 16 bit width") {
            uint dataWidth = 16;
            uint inputsPerClock = 2;
            uint kernelWidth = 3;
            uint elementWidth = 16;

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"in", c->BitIn()->Arr(elementWidth)->Arr(inputsPerClock)},
                    {"out", c->Bit()->Arr(elementWidth)->Arr(inputsPerClock)},
                    {"valid", c->Bit()}                        
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainConv1DTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Values conv1DGenArgs = {
                {"dataWidth", Const::make(c, dataWidth)},
                {"inputsPerClock", Const::make(c, inputsPerClock)},
                {"kernelWidth", Const::make(c, kernelWidth)},
                {"elementWidth", Const::make(c, elementWidth)},
            };

            string conv1DName = "conv1D_test";
            Instance* conv1D = def->addInstance(conv1DName, "aetherlinglib.conv1D", conv1DGenArgs);
            string wenModule = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            def->connect(wenModule + ".out.0", conv1DName + ".wen");
            // create different input for each element of kernel
            for (uint i = 0 ; i < kernelWidth; i++) {
                string constName = "constInput" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, elementWidth)}},
                    {{"value", Const::make(c, elementWidth, i)}});

                def->connect(constName + ".out", conv1DName + ".in.kernel." + to_string(i));
            }

            def->connect("self.in", conv1DName + ".in.data");
            def->connect(conv1DName + ".out", "self.out");
            def->connect(conv1DName + ".valid", "self.valid");

            mainModule->setDef(def);
            mainModule->print();
            conv1D->getModuleRef()->print();

            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();
                                    
            SimulatorState state(mainModule);
            // pass in increasing numbers each clock cycle, should get 1*2*3 times that number
            // once valid is right, should get items out in same order sent in           
            for (uint clkCount = 0, numValidClks = 0; numValidClks < dataWidth / inputsPerClock ; clkCount++) {
                state.setClock("self.clk", 0, 1); // get a new rising clock edge
                // set the input
                for (uint inputIdx = 0; inputIdx < inputsPerClock; inputIdx++) {
                    state.setValue("self.in_" + to_string(inputIdx), BitVector(elementWidth,
                                                                    clkCount*inputsPerClock + inputIdx));
                }
                state.exeCombinational();
                // should be valid starting on cycle (kernelWidth + inputsPerClock - 1) / inputsPerClock
                // note: subtract 1 more for 0 indexing
                if (clkCount < (kernelWidth + inputsPerClock - 1) / inputsPerClock - 1) {
                    REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
                }
                else {
                    REQUIRE(state.getBitVec("self.valid") == BitVector(1, 1));
                    // verify that the output for each input per clock is offset by 1 pixel
                    for (uint inputIdx = 0; inputIdx < inputsPerClock; inputIdx++) {
                        // now check that the n, n+1, ..., n+(kernelWidth-1) inputs are used to produce output
                        // on nth clock cycle of valid
                        uint rightOutput = 0;
                        for (uint i = 0; i < kernelWidth; i++) {
                            rightOutput += (numValidClks*inputsPerClock+inputIdx+i)*i;
                        }
                        REQUIRE(state.getBitVec("self.out_" + to_string(inputIdx)) ==
                                BitVector(elementWidth, rightOutput));

                    }
                    numValidClks++;
                }
                state.exeSequential();
            }
        }
        deleteContext(c);
    }
}
