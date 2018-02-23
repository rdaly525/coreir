#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>
#include <iostream>

using namespace std;
using namespace CoreIR;

void Aetherling_createStreamifyArrayifyGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    /*
     * inputType - the type that you want to flatten
     * outputType - what you want to flatten it into, inputType must be some set of arrays of this
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
                    {"reset", c->BitIn()}
                        //{"emittedAllElements", c->Bit()} // this bit is 1 once all the elements of the array
                    // have been emitted to the stream
                });
        });

    Generator* streamify =
        aetherlinglib->newGeneratorDecl("streamify", aetherlinglib->getTypeGen("streamify_type"), streamifyArrayifyParams);

    streamify->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* elementType = genargs.at("elementType")->get<Type*>();
            uint arrayLength = genargs.at("arrayLength")->get<int>();
            uint elementWidth = elementType->getSize()

            Values hydratedType({
                    {"hydratedType", Const::make(c, elementType)}
                });
            Module* dehydrateInput = c->getGenerator("aetherlinglib.dehydrate")->getModule(hydratedType);

            // serializer will choose 1 input at a time, dehydrate converts complex types to bit arrays
            // hydrate converts them back
            def->addInstance("dehydrateForSerializer", "aetherlinglib.mapN", {
                    {"numInputs", Const::make(c, numInputs)},
                    {"operator", Const::make(c, dehydrateInput)}
                });

            def->addInstance("serializer", "commonlib.seralizer", {
                    {"width", elementWidth},
                    {"rate", numInputs}
                });
            def->addInstance("hydrateForSerializer", "aetherlinglib.hydrate", hydratedType);
            def->addInstance("notFinishedCycle", "coreir.not", {{"width", Const::make(c, 1)}});
            def->addInstance("enOr", "coreir.or", {{"width", Const::make(c, 1)}});

            /*
            // these will emit 1 as long as count of serializer isn't max count and should keep going
            def->addInstance("countEq", "coreir.eq", {{"width", Const::make(c, elementWidth)}});
            string lastElement = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, width, numInputs));
            // this register will emit 1 the cycle after streamify has gone trhough all elements
            // reset will clear it to 0 to show that not all elements have been emitted
            def->addInstance("emittedAllReg", "coreir.reg", {
                    {"width", Const::make(c, 1)},
                    {"has_en", Const::make(c, true)},
                    {"has_clr", Const::make(c, true)},
                    {"has_rst", Const::make(c, false)} // note: this is asynchronous, clear is what
                    // I want as it is synchronous
                });
            */
            // emit the constant 1 for enabling the seralizler
            //string enableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));

            def->connect("self.in", "dehydrateForSeralizer.in");
            def->connect("self.reset", "serializer.reset");
            def->connect("dehydrateForSeralizer.out", "serializer.in");
            def->connect("serializer.out", "hydrateForSerializer.in");
            def->connect("hydrateForSerializer.out", "self.out");
            // as long as haven't reached the end of the array, keep emitting elements
            def->connect("serializer.finishedCycle", "notFinishedCycle.in");
            // keep emmitting elements as long as haven't hit end
            def->connect("notFinishedCycle.out", "enOr.in0");
            // if hit end and reset, go back to the beginning
            def->connect("self.reset", "enOr.in1");
            def->connect("enOr.out", "serializer.en");
            // def->connect(enableConst + ".out", "serializer.en");
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
                    {"reset", c->BitIn()}
                        //{"emittedAllElements", c->Bit()} // this bit is 1 once all the elements of the array
                    // have been emitted to the stream
                });
        });

    Generator* arrayify =
        aetherlinglib->newGeneratorDecl("arrayify", aetherlinglib->getTypeGen("arrayify_type"), streamifyArrayifyParams);

    arrayify->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* elementType = genargs.at("elementType")->get<Type*>();
            uint arrayLength = genargs.at("arrayLength")->get<int>();
            uint elementWidth = elementType->getSize()

            Values hydratedType({
                    {"hydratedType", Const::make(c, elementType)}
                });

            // deserializer will take in 1 input at a time and emit them all at the end,
            // dehydrate converts complex types to bit arrays
            // hydrate converts them back

            def->addInstance("dehydrateForDeserializer", "aetherlinglib.dehydrate", hydratedType);  

            def->addInstance("deserializer", "commonlib.deseralizer", {
                    {"width", elementWidth},
                    {"rate", numInputs}
                });

            Module* hydrateOutput = c->getGenerator("aetherlinglib.hydrate")->getModule(hydratedType);
            def->addInstance("hydrateForDeserializer", "aetherlinglib.mapN", {
                    {"numInputs", Const::make(c, numInputs)},
                    {"operator", Const::make(c, hydrateOutput)}
                });
          
            /*
            // these will emit 1 as long as count of serializer isn't max count and should keep going
            def->addInstance("countEq", "coreir.eq", {{"width", Const::make(c, elementWidth)}});
            string lastElement = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, width, numInputs));
            // this register will emit 1 the cycle after streamify has gone trhough all elements
            // reset will clear it to 0 to show that not all elements have been emitted
            def->addInstance("emittedAllReg", "coreir.reg", {
                    {"width", Const::make(c, 1)},
                    {"has_en", Const::make(c, true)},
                    {"has_clr", Const::make(c, true)},
                    {"has_rst", Const::make(c, false)} // note: this is asynchronous, clear is what
                    // I want as it is synchronous
                });
            */
            // emit the constant 1 for enabling the seralizler
            //string enableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));

            def->connect("self.in", "dehydrateForDeseralizer.in");
            def->connect("self.reset", "deserializer.reset");
            def->connect("selfDeseralizer.out", "deserializer.in");
            def->connect("deserializer.out", "hydrateForDeserializer.in");
            def->connect("hydrateForDeserializer.out", "self.out");
            // def->connect(enableConst + ".out", "serializer.en");
        });
}
