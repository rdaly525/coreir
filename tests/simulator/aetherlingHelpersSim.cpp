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

    TEST_CASE("Simulate hydration from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        SECTION("aetherlinglib dehydrate and rehydrate") {
            uint width = 16;
            uint parallelOperators = 4;
            uint constInput = 3;

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);

            Type* twoArrays = c->Record({
                    {"container",c->Record({
                                {"el1", c->BitIn()->Arr(width)},
                                {"el0", c->BitIn()->Arr(width)}
                            })}
                });

            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Out(twoArrays)}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("hydrationTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            string el0InputModule = Aetherling_addCoreIRConstantModule(c, def, width, Const::make(c, width, 5));
            string el1InputModule = Aetherling_addCoreIRConstantModule(c, def, width, Const::make(c, width, 10));

            def->addInstance("dehydrate", "aetherlinglib.dehydrate",
                                       {{"hydratedType", Const::make(c, twoArrays)}});

            def->addInstance("hydrate", "aetherlinglib.hydrate",
                                       {{"hydratedType", Const::make(c, twoArrays)}});

            def->connect(el0InputModule + ".out", "dehydrate.in.container.el0");
            def->connect(el1InputModule + ".out", "dehydrate.in.container.el1");
            def->connect("dehydrate.out", "hydrate.in");
            def->connect("hydrate.out", "self.out");

            mainModule->setDef(def);
            c->runPasses({"rungenerators", "flatten", "flattentypes"});
            mainModule->print();

            SimulatorState state(mainModule);
            state.execute();
            REQUIRE(state.getBitVec("self.out_container_el0") == BitVector(width, 5));
            REQUIRE(state.getBitVec("self.out_container_el1") == BitVector(width, 10));
        }
        deleteContext(c);
    }

     TEST_CASE("Simulate streamify/arrayify from aetherlinglib") {
        // New context
        Context* c = newContext();
        Namespace* g = c->getGlobal();

        SECTION("aetherlinglib streamify and arrayify") {
            uint width = 16;
            uint parallelInputs = 4;
            uint constInput = 3;

            CoreIRLoadLibrary_commonlib(c);
            CoreIRLoadLibrary_aetherlinglib(c);

            Type* twoArrays = c->Record({
                    {"container",c->Record({
                                {"el1", c->BitIn()->Arr(width)},
                                {"el0", c->BitIn()->Arr(width)}
                            })}
                });

            // create the main module to run the test on the adder
            Type* mainModuleType = c->Record({
                    {"out", c->Out(twoArrays->Arr(parallelInputs))},
                    {"ready", c->Bit()},
                    {"valid", c->Bit()}
                });
            Module* mainModule = c->getGlobal()->newModuleDecl("streamifyTest", mainModuleType);
            ModuleDef* def = mainModule->newModuleDef();

            Values streamifyParams{
                {"elementType", Const::make(c, twoArrays)},
                {"arrayLength", Const::make(c, parallelInputs)}
            };

            def->addInstance("streamify", "aetherlinglib.streamify", streamifyParams);
            def->addInstance("arrayify", "aetherlinglib.arrayify", streamifyParams);

            for (uint i = 0; i < parallelInputs; i++) {
                string el0InputModule = Aetherling_addCoreIRConstantModule(c, def, width,
                                                                           Const::make(c, width, parallelInputs*(i+1)));
                string el1InputModule = Aetherling_addCoreIRConstantModule(c, def, width,
                                                                           Const::make(c, width, (parallelInputs+1)*(i+1)));
                string idx = to_string(i);
                def->connect(el0InputModule + ".out", "streamify.in." + idx + ".container.el0");
                def->connect(el1InputModule + ".out", "streamify.in." + idx + ".container.el1");
            }
                
            def->connect("streamify.out", "arrayify.in");
            def->connect("arrayify.out", "self.out");

            // handle the administrative stuff
            string enableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            string disableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 0));
            def->connect(enableConst + ".out.0", "streamify.en");
            def->connect(disableConst + ".out.0", "streamify.reset");
            def->connect(enableConst + ".out.0", "arrayify.en");
            def->connect(disableConst + ".out.0", "arrayify.reset");
            def->connect("streamify.ready", "self.ready");
            def->connect("arrayify.valid", "self.valid");

            mainModule->setDef(def);
            c->runPasses({"rungenerators", "verifyconnectivity-onlyinputs-noclkrst",
                        "wireclocks-coreir", "flatten", "flattentypes", "verifyconnectivity",
                        "deletedeadinstances"},
                {"aetherlinglib", "commonlib", "mantle", "coreir", "global"});
            mainModule->print();
    
            SimulatorState state(mainModule);
            state.setClock("self.clk", 0, 1); // get a new rising clock edge
            // on first cycle, ready should be asserted, then deasserted for rest until processed all input
            // from start until all inputs have gone through, valid should be deasserted
            // note: 4 clock cycles, which means 3 edges as first clock is on
            for (uint i = 0; i < parallelInputs - 1; i++) {
                state.exeCombinational();
                REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
                REQUIRE(state.getBitVec("self.ready") == BitVector(1, i % parallelInputs == 0 ? 1 : 0));
                state.exeSequential();
            }
            state.exeCombinational();
            REQUIRE(state.getBitVec("self.ready") == BitVector(1, 0));
            REQUIRE(state.getBitVec("self.valid") == BitVector(1, 1));
            for (uint i = 0; i < parallelInputs; i++) {
                string idx = to_string(i);
                REQUIRE(state.getBitVec("self.out_" + idx + "_container_el0") == BitVector(width, parallelInputs*(i+1)));
                REQUIRE(state.getBitVec("self.out_" + idx + "_container_el1") == BitVector(width, (parallelInputs+1)*(i+1)));
            }
            state.exeSequential();
            state.exeCombinational();
            REQUIRE(state.getBitVec("self.ready") == BitVector(1, 1));
            REQUIRE(state.getBitVec("self.valid") == BitVector(1, 0));
        }
        deleteContext(c);
    }
}
