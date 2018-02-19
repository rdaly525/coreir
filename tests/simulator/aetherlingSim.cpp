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

    TEST_CASE("Simulate mapN from aetherlinglib") {

        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        SECTION("aetherlinglib mapN with 4 mul, 3 as constant, 16 bit width") {
            uint width = 16;
            uint parallelOperators = 4;
            uint constInput = 3;

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);

            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Bit()->Arr(width)->Arr(parallelOperators)}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainMapNMulTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Type* twoInZippedOneOutGenType = c->Record({
                    {"in",c->Record({
                                {"el0", c->BitIn()->Arr(width)},
                                {"el1", c->BitIn()->Arr(width)}
                            })},
                    {"out",c->Bit()->Arr(width)}
                });

            /* creating the mulBy2 that the mapN will parallelize */
            Module* mul2Inputs = c->getGlobal()->newModuleDecl("mul2Inputs", twoInZippedOneOutGenType);
            ModuleDef* mul2InputsDef = mul2Inputs->newModuleDef();        

            mul2InputsDef->addInstance("mul", "coreir.mul", {{"width", Const::make(c, width)}});
            mul2InputsDef->connect("self.in.el0", "mul.in0");
            mul2InputsDef->connect("self.in.el1", "mul.in1");
            mul2InputsDef->connect("mul.out", "self.out");
            mul2Inputs->setDef(mul2InputsDef);

            Values zip2Params({
                    {"numInputs", Const::make(c, parallelOperators)},
                    {"input0Type", Const::make(c, c->BitIn()->Arr(width))},
                    {"input1Type", Const::make(c, c->BitIn()->Arr(width))}
                });
    
            Values mapNParams({
                    {"parallelOperators", Const::make(c, parallelOperators)},
                    {"operator", Const::make(c, mul2Inputs)}
                });

            def->addInstance("zip2", "aetherlinglib.zip2", zip2Params);
            string mapNName = "map" + to_string(parallelOperators);
            Instance* mapN_mul = def->addInstance(mapNName, "aetherlinglib.mapN", mapNParams);

            // here we are wiring up a constant value and an iterated one to each input of the zip before
            // it goes into the map
            string notIteratedConstModule = Aetherling_addCoreIRConstantModule(c, def, width, Const::make(c, width, constInput));

            for (uint i = 0 ; i < parallelOperators; i++) {
                string constName = "constInput" + to_string(i);
                def->connect(notIteratedConstModule + ".out", "zip2.in0." + to_string(i));
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, width)}},
                    {{"value", Const::make(c, width, i)}});

                def->connect(constName + ".out",  "zip2.in1." + to_string(i));
            }

            def->connect("zip2.out", mapNName + ".in");
            def->connect(mapNName + ".out", "self.out");
            
            mainModule->setDef(def);
            mapN_mul->getModuleRef()->print();
            c->runPasses({"rungenerators", "flatten", "flattentypes"});
            mainModule->print();
            //mapN_mul->getModuleRef()->print();

            SimulatorState state(mainModule);
            state.execute();
            
            for (uint i = 0; i < parallelOperators; i++) {
                REQUIRE(state.getBitVec("self.out_" + to_string(i)) == BitVector(width, i*constInput));
            }
                    
        }

        deleteContext(c);
    }

    TEST_CASE("Simulate reduceNSerializable from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        SECTION("aetherlinglib reduceN with 4 inputs, coreir.add as op, 16 bit width") {
            uint width = 16;
            uint numLayers = 3;
            uint constInput = 3;

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Bit()->Arr(width)}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainReduceNTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Module* add = c->getGenerator("coreir.add")->getModule({{"width", Const::make(c, width)}});
            add->print();

            Values reduceNModArgs = {
                {"numLayers", Const::make(c, numLayers)},
                {"operator", Const::make(c, add)}
            };
            
            string reduceNName = "reduce" + to_string(numLayers);
            Instance* reduceN_add = def->addInstance(reduceNName, "aetherlinglib.reduceNSerializable", reduceNModArgs);
            // create different input for each operator
            uint rightOutput = 0;
            for (uint i = 0 ; i < pow(2, numLayers); i++) {
                string constName = "constInput" + to_string(i);
                def->addInstance(
                    constName,
                    "coreir.const",
                    {{"width", Const::make(c, width)}},
                    {{"value", Const::make(c, width, i)}});

                def->connect(constName + ".out", reduceNName + ".in." + to_string(i));
                rightOutput += i;
            }

            def->addInstance("dontMergeCur","coreir.const",
                             {{"width", Const::make(c, 1)}}, {{"value", Const::make(c,1,0)}});
            def->connect("dontMergeCur.out.0", reduceNName + ".mergeCur");
            def->connect(reduceNName + ".out", "self.out");
            mainModule->setDef(def);
            mainModule->print();
            reduceN_add->getModuleRef()->print();
            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst", "flatten", "verifyconnectivity-onlyinputs-noclkrst", "flattentypes", "wireclocks-coreir"});
            mainModule->print();
                                    
            SimulatorState state(mainModule);
            state.setClock("self.clk", 0, 1); // get a new rising clock edge
            state.execute();

            REQUIRE(state.getBitVec("self.out") == BitVector(width, rightOutput));
        }
        deleteContext(c);
    }

    TEST_CASE("Simulate convolution from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        SECTION("aetherlinglib conv1D with 9 values for data, 3 values for kernel, 1 value input per clock, 16 bit width") {
            uint dataWidth = 9;
            uint inputPerClockWidth = 1;
            uint kernelWidth = 3;
            uint elementWidth = 16;

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);
            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"in", c->BitIn()->Arr(elementWidth)->Arr(inputPerClockWidth)},
                    {"out", c->Bit()->Arr(elementWidth)},
                    {"valid", c->Bit()}                        
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("mainConv1DTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Values conv1DGenArgs = {
                {"dataWidth", Const::make(c, dataWidth)},
                {"inputPerClockWidth", Const::make(c, inputPerClockWidth)},
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
            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst", "flatten", "verifyconnectivity-onlyinputs-noclkrst", "flattentypes", "wireclocks-coreir"});
            //c->runPasses({"rungenerators", "flatten", "flattentypes", "wireclocks-coreir"});
            mainModule->print();
                                    
            SimulatorState state(mainModule);
            // pass in increasing numbers each clock cycle, should get 1*2*3 times that number
            // once valid is right, should get items out in same order sent in           
            for (uint clkCount = 0, numValidClks = 0; numValidClks < dataWidth ; clkCount++) {
                state.setClock("self.clk", 0, 1); // get a new rising clock edge
                // set the input
                state.setValue("self.in_0", BitVector(elementWidth, clkCount));
                state.exeCombinational();
                cout<< "self.in_0: " << state.getBitVec("self.in_0") << endl;
                cout<< "conv1D_test$conv1DLineBuffer$reg_1.out" << state.getBitVec("conv1D_test$conv1DLineBuffer$reg_1.out") << endl;
                cout<< "conv1D_test$conv1DLineBuffer$reg_2.out" << state.getBitVec("conv1D_test$conv1DLineBuffer$reg_2.out") << endl;


                // should take kernelWidth/inputPerClockWidth cycles before valid, then stay valid for rest
                // note that timing is off slightly as this is a 0 latency linebuffer
                if (clkCount < kernelWidth/inputPerClockWidth - 1) {
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
                    cout<<"constInput0: " << state.getBitVec("constInput0.out") << endl;
                    cout<<"mul0 in0: " << state.getBitVec("conv1D_test$conv1DMap$op_0$wrappedInstance_mul_U5.in0") << ", mul0 in1: " << state.getBitVec("conv1D_test$conv1DMap$op_0$wrappedInstance_mul_U5.in1") << endl;
                    cout<<"mul1 in0: " << state.getBitVec("conv1D_test$conv1DMap$op_1$wrappedInstance_mul_U5.in0") << ", mul1 in1: " << state.getBitVec("conv1D_test$conv1DMap$op_1$wrappedInstance_mul_U5.in1") << endl;
                    cout<<"mul2 in0: " << state.getBitVec("conv1D_test$conv1DMap$op_2$wrappedInstance_mul_U5.in0") << ", mul2 in1: " << state.getBitVec("conv1D_test$conv1DMap$op_2$wrappedInstance_mul_U5.in1") << endl;
                    cout<< "out bitvec" << state.getBitVec("self.out") << endl;
                    //assert(0);
                    REQUIRE(state.getBitVec("self.out") == BitVector(elementWidth, rightOutput));
                    numValidClks++;
                    //assert(0);
                    //assert(1);
                }
                state.exeSequential();
            }
        }
        deleteContext(c);
    }
}
