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
            Module* mainModule = c->getGlobal()->newModuleDecl("mainMapNMulTest", mainModuleType);
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
}
