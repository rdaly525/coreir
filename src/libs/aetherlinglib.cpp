#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include "aetherlinglib/aeMap.h"
#include "aetherlinglib/aeReduce.h"
#include "aetherlinglib/aeZip2.h"
#include "aetherlinglib/aeConv.h"
#include "aetherlinglib/aeFlatten.h"
#include "aetherlinglib/aeDehydrate.h"
#include "aetherlinglib/aeStreamifyArrayify.h"
#include "aetherlinglib/aeOverlapPartition.h"
#include <string>

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(aetherlinglib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_aetherlinglib(Context* c) {

    Namespace* aetherlinglib = c->newNamespace(AETHERLING_NAMESPACE);

    /////////////////////////////////
    // Create all the different generators
    /////////////////////////////////

    Aetherling_createMapGenerator(c);
    Aetherling_createReduceGenerator(c);
    Aetherling_createZipGenerator(c);
    Aetherling_createConvGenerator(c);
    Aetherling_createFlattenGenerator(c);
    Aetherling_createHydrateAndDehydrateGenerators(c);
    Aetherling_createStreamifyArrayifyGenerator(c);
    Aetherling_createOverlapPartitionGenerator(c);

    // create a generator to convert two argument modules into one argument
    // modules with a fixed constant for one input
    // note that the input to the constant gets assigned the second input to the two argument module
    // WHILE THIS IS INTERESTING AND SHOULD WORK, doesn't becuase it is a generator that produces a module and
    // modules can't be passed as inputs to generators, only other generators can. I need to convert this int
    // a function that produces generators, will do later
    Params op2To1Params = Params({
            {"width", c->Int()},
            {"constant", c->Int()},
            {"operator", c->String()}
        });

    aetherlinglib->newTypeGen(
        "op2To1_type",
        op2To1Params,
        [](Context* c, Values genargs) {
            uint width = genargs.at("width")->get<int>();
            return c->Record({
                    {"in", c->BitIn()->Arr(width)},
                    {"out", c->Bit()->Arr(width)}
                });
        });

    Generator* op2To1 =
        aetherlinglib->newGeneratorDecl("op2To1", aetherlinglib->getTypeGen("op2To1_type"), op2To1Params);

    op2To1->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint width = genargs.at("width")->get<int>();
            uint constant = genargs.at("constant")->get<int>();
            string op = genargs.at("operator")->get<string>();
            assert(width>0);

            Const* aWidth = Const::make(c, width);

            def->addInstance("baseOp", op, {{"width", aWidth}});
            def->addInstance("constIn","coreir.const",
                             {{"width", aWidth}},{{"value",Const::make(c,width,constant)}});

            def->connect("self.in", "baseOp.in.0");
            def->connect("constIn.out", "baseOp.in.1");
            def->connect("baseOp.out", "self.out");
        });

    return aetherlinglib;  
}

string Aetherling_addCoreIRConstantModule(Context* c, ModuleDef* def, uint width, Const* val) {
    string valName = val->toString();
    replace(valName.begin(), valName.end(), '\'', '-');
    string constName = "constInput_" + valName;
    def->addInstance(
        constName,
        "coreir.const",
        {{"width", Const::make(c,width)}},
        {{"value", val}});
    return constName;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(aetherlinglib);
