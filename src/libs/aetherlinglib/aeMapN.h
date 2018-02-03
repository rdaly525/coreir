#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>

using namespace std;
using namespace CoreIR;

void Aetherling_createMapGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * width - the width in bits of each input
     * parallelOperatrs - how many operators to have in parallel
     * operator - the operator to parallelize. Note that it must have one input known as "in" and 
     * one output known as "out"
     */
    Params mapNparams = Params({
            //{"width", c->Int()},
            {"parallelOperators", c->Int()},
            {"operator", ModuleType::make(c)}
        });

    aetherlinglib->newTypeGen(
        "mapN_type", // name for typegen
        mapNparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            //uint width = genargs.at("width")->get<int>();
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in")->Arr(parallelOperators)},
                    {"out", opType->sel("out")->Arr(parallelOperators)}
                    //{"in", c->BitIn()->Arr(width)->Arr(parallelOperators)},
                    //{"out", c->Bit()->Arr(width)->Arr(parallelOperators)}
                });
        });

    Generator* mapN =
        aetherlinglib->newGeneratorDecl("mapN", aetherlinglib->getTypeGen("mapN_type"), mapNparams);

    mapN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            //uint width = genargs.at("width")->get<int>();
            uint parallelOperators = genargs.at("parallelOperators")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            //Type* inputType = genargs.at("inputType")->get<Type*>();
            //Type* outputType = genargs.at("outputType")->get<Type*>();
            assert(parallelOperators>0);
            //assert(width>0);
            //RecordType* inputTypeRecord = dynamic_cast<RecordType*>(inputType);
            //assert(inputTypeRecord != 0); // 0 if cast failed, so input type wasn't RecordType
            //RecordType* outputTypeRecord = dynamic_cast<RecordType*>(outputType);
            //assert(outputTypeRecord != 0); // 0 if cast failed, so output type wasn't RecordType
            //opModule->getType()->sel("in")->print();
            //inputType->print();
            //assert(opModule->getType()->sel("in") == inputType); // ensure input type maps module type
            
            // now create each op and wire the inputs and outputs to it
            for (uint i = 0; i < parallelOperators; i++) {
                string idxStr = to_string(i);                
                string opStr = "op_" + idxStr;
                def->addInstance(opStr, opModule);
                def->connect("self.in." + idxStr, opStr + ".in");
                def->connect(opStr + ".out", "self.out." + idxStr);
            }
        });
}
