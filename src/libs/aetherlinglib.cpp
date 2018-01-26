#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <vector>

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(aetherlinglib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_aetherlinglib(Context* c) {

    Namespace* aetherlinglib = c->newNamespace("aetherlinglib");

    /////////////////////////////////
    // Aetherlingliblib Types
    /////////////////////////////////

    Params widthparams = Params({{"width",c->Int()}});

    Params mapNparams = Params({
            {"width", c->Int()},
            {"parallelOperators", c->Int()},
            //{"inputType", CoreIRType::make(c)},
            //{"outputType", CoreIRType::make(c)},
            {"operator", ModuleType::make(c)}
        });

    aetherlinglib->newTypeGen(
        "mapN_type", // name for typegen
        mapNparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint width = genargs.at("width")->get<int>();
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            //Type* inputType = genargs.at("inputType")->get<Type*>;
            //Type* outputType = genargs.at("outputType")->get<Type*>;
            return c->Record({
                    //{"in", input_type->Arr(parallelOperators)},
                    //{"out", output_type->Arr(parallelOperators)}
                    {"in", c->BitIn()->Arr(width)->Arr(parallelOperators)},
                    {"out", c->Bit()->Arr(width)->Arr(parallelOperators)}
                });
        });

    Generator* mapN =
        aetherlinglib->newGeneratorDecl("mapN", aetherlinglib->getTypeGen("mapN_type"), mapNparams);

    mapN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint width = genargs.at("width")->get<int>();
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            //Type* inputType = genargs.at("inputType")->get<Type*>;
            //Type* outputType = genargs.at("outputType")->get<Type*>;
            assert(parallelOperators>0);
            assert(width>0);
            /*RecordType* inputTypeRecord = dynamic_cast<RecordType*>(inputType);
            assert(inputTypeRecord != 0); // 0 if cast failed, so input type wasn't RecordType
            RecordType* outputTypeRecord = dynamic_cast<RecordType*>(outputType);
            assert(outputTypeRecord != 0); // 0 if cast failed, so output type wasn't RecordType
            */
                     
            // now create each op and wire the inputs and outputs to it
            for (int i = 0; i < parallelOperators; i++) {
                string idxStr = to_string(i);                
                string opStr = "op_" + idxStr;
                def->addInstance(opStr, opModule, {{}});
                def->connect("self.in." + idxStr, opStr + ".in");
                def->connect(opStr + ".out", "self.out." + idxStr);
            }
             
        });

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

string Aetherling_addCoreIRConstantModule(Context* c, ModuleDef* def, uint width, BitVector bv) {
    stringstream bvStr;
    bvStr << bv;
    string constName = "constInput_" + bvStr.str();
    def->addInstance(
        constName,
        "coreir.const",
        {{"width", Const::make(c,width)}},
        {{"value", Const::make(c,bv)}});
    return constName;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(aetherlinglib)
