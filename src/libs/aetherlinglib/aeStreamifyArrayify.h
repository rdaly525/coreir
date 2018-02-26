#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>
#include <iostream>

using namespace std;
using namespace CoreIR;

void Aetherling_createStreamifyArrayifyGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    /*
     * elementType - the type that the stream/array contains
     * arrayLength - how wide arrays should be received/emmitted
     */
    Params streamifyArrayifyParams = Params({
            {"elementType", CoreIRType::make(c)},
            {"arrayLength", c->Int()}
        });

    aetherlinglib->newTypeGen(
        "streamify_type", // name for typegen
        streamifyArrayifyParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            Type* elementType = genargs.at("elementType")->get<Type*>();
            uint arrayLength = genargs.at("arrayLength")->get<int>();
            return c->Record({
                    {"in", c->In(elementType->Arr(arrayLength))},
                    {"out", c->Out(elementType)},
                    {"reset", c->BitIn()},
                    {"en", c->BitIn()},
                    {"ready", c->Bit()}
                });
        });

    Generator* streamify =
        aetherlinglib->newGeneratorDecl("streamify", aetherlinglib->getTypeGen("streamify_type"), streamifyArrayifyParams);

    streamify->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* elementType = genargs.at("elementType")->get<Type*>();
            uint arrayLength = genargs.at("arrayLength")->get<int>();
            uint elementWidth = elementType->getSize();

            Values hydratedType({
                    {"hydratedType", Const::make(c, elementType)}
                });
            Module* dehydrateInput = c->getGenerator("aetherlinglib.dehydrate")->getModule(hydratedType);

            // serializer will choose 1 input at a time, dehydrate converts complex types to bit arrays
            // hydrate converts them back
            def->addInstance("dehydrateForSerializer", "aetherlinglib.mapParallel", {
                    {"numInputs", Const::make(c, arrayLength)},
                    {"operator", Const::make(c, dehydrateInput)}
                });

            def->addInstance("serializer", "commonlib.serializer", {
                    {"width", Const::make(c, elementWidth)},
                    {"rate", Const::make(c, arrayLength)}
                });
            def->addInstance("hydrateForSerializer", "aetherlinglib.hydrate", hydratedType);

            def->connect("self.in", "dehydrateForSerializer.in");
            def->connect("self.reset", "serializer.reset");
            def->connect("dehydrateForSerializer.out", "serializer.in");
            def->connect("self.en", "serializer.en");
            def->connect("serializer.out", "hydrateForSerializer.in");
            def->connect("hydrateForSerializer.out", "self.out");
            // in this version, never stop, always keep looping over array to produce stream
            // ready says when able to take next array
            def->connect("serializer.ready", "self.ready");
        });

    aetherlinglib->newTypeGen(
        "arrayify_type", // name for typegen
        streamifyArrayifyParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            Type* elementType = genargs.at("elementType")->get<Type*>();
            uint arrayLength = genargs.at("arrayLength")->get<int>();
            return c->Record({
                    {"in", c->In(elementType)},
                    {"out", c->Out(elementType->Arr(arrayLength))},
                    {"reset", c->BitIn()},
                    {"en", c->BitIn()},
                    {"valid", c->Bit()} // this bit is 1 once all the elements of the array
                    // have been emitted to the stream
                });
        });

    Generator* arrayify =
        aetherlinglib->newGeneratorDecl("arrayify", aetherlinglib->getTypeGen("arrayify_type"), streamifyArrayifyParams);

    arrayify->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* elementType = genargs.at("elementType")->get<Type*>();
            uint arrayLength = genargs.at("arrayLength")->get<int>();
            uint elementWidth = elementType->getSize();

            Values hydratedType({
                    {"hydratedType", Const::make(c, elementType)}
                });

            // deserializer will take in 1 input at a time and emit them all at the end,
            // dehydrate converts complex types to bit arrays
            // hydrate converts them back

            def->addInstance("dehydrateForDeserializer", "aetherlinglib.dehydrate", hydratedType);  

            def->addInstance("deserializer", "commonlib.deserializer", {
                    {"width", Const::make(c, elementWidth)},
                    {"rate", Const::make(c, arrayLength)}
                });

            Module* hydrateOutput = c->getGenerator("aetherlinglib.hydrate")->getModule(hydratedType);
            def->addInstance("hydrateForDeserializer", "aetherlinglib.mapParallel", {
                    {"numInputs", Const::make(c, arrayLength)},
                    {"operator", Const::make(c, hydrateOutput)}
                });

            def->connect("self.in", "dehydrateForDeserializer.in");
            def->connect("deserializer.valid", "self.valid");
            def->connect("self.en", "deserializer.en");
            def->connect("self.reset", "deserializer.reset");
            def->connect("dehydrateForDeserializer.out", "deserializer.in");
            def->connect("deserializer.out", "hydrateForDeserializer.in");
            def->connect("hydrateForDeserializer.out", "self.out");
        });
}
