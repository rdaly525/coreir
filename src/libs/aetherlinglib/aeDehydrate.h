#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>
#include <iostream>
#include <queue>
#include <tuple>

using namespace std;
using namespace CoreIR;

/*
 * Since same process for dehydrate and hydrate, just wiring in different direction, reusing logic
 */
void walkTypeTree(ModuleDef* def, uint dehydratedSize, queue<tuple<Type*,string>>& elementsToExamine) {
    // go through every type
    for (int curDehydratedIndex = 0; !elementsToExamine.empty();) { 
        // get the next type and its name
        auto curElement = elementsToExamine.front();
        elementsToExamine.pop();
        Type* curType = get<0>(curElement);
        string curName = get<1>(curElement);

        // add its children elements to the queue if its not a bit, or wire up the bits
        switch(curType->getKind()) {
        case Type::TypeKind::TK_Bit : // if non-array of bits type is output, hydrate as hydrate
            // converts arrays of bits to original types
            def->connect("self.in." + to_string(curDehydratedIndex), curName);
            curDehydratedIndex++; // output on next wire
            break;
        case Type::TypeKind::TK_BitIn : // if non-array of bits type is input, dehydrate as converting any type
            // to array of bits
            def->connect(curName, "self.out." + to_string(curDehydratedIndex));
            curDehydratedIndex++; // output on next wire
            break;
        case Type::TypeKind::TK_Array : {
            ArrayType* curAsArr = dyn_cast<ArrayType>(curType);
            Type* elemType = curAsArr->getElemType();
            for (uint i = 0; i < curAsArr->getLen(); i++) {
                elementsToExamine.push(make_tuple(elemType, curName + "." + to_string(i)));
            }
            break;
        }
        case Type::TypeKind::TK_Record : {
            RecordType* curAsRec = dyn_cast<RecordType>(curType);
            auto nameTypeMap = curAsRec->getRecord();
            for (auto it = nameTypeMap.begin(); it != nameTypeMap.end(); ++it) {
                elementsToExamine.push(make_tuple(it->second, curName + "." + it->first));
            }
            break;
        }
        case Type::TypeKind::TK_Named : {
            ASSERT(0, "hydrating or dehydrating named types not supported");
        }
        default : ASSERT(0, "hydrating or dehydrating invalid type " + curType->toString());
        }
    }
}

/* Dehydrate converts a nested structure into an array of bits that can be passed to muxes, serializers,
 * and other objects that can't handle complex types 
 * Note: unlike flatten, don't need get size as all types already have a getsize that gives number of bits
 */

void Aetherling_createHydrateAndDehydrateGenerators(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    /*
     * hydratedType - the type that you want to dehydrate to/from just bits
     */
    Params hydrateParams = Params({
            {"hydratedType", CoreIRType::make(c)}
        });

    aetherlinglib->newTypeGen(
        "dehydrate_type", // name for typegen
        hydrateParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            Type* inputType = genargs.at("hydratedType")->get<Type*>();
            uint outputSize = inputType->getSize();
            return c->Record({
                    {"in", c->In(inputType)},
                    {"out", c->Bit()->Arr(outputSize)}
                });
        });

    Generator* dehydrate =
        aetherlinglib->newGeneratorDecl("dehydrate", aetherlinglib->getTypeGen("dehydrate_type"), hydrateParams);

    dehydrate->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* inputType = c->In(genargs.at("hydratedType")->get<Type*>());
            uint outputSize = inputType->getSize();
            // note: this gets a value for each element, so if an array has n elements, this gets
            // pushed n times
            // the string is the name of the type
            queue<tuple<Type*,string>> elementsToExamine;
            // first element to examine is hydrated input and its name relative to root
            elementsToExamine.push(make_tuple(inputType, "self.in"));

            walkTypeTree(def, outputSize, elementsToExamine);
        });

    aetherlinglib->newTypeGen(
        "hydrate_type", // name for typegen
        hydrateParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            Type* outputType = genargs.at("hydratedType")->get<Type*>();
            uint inputSize = outputType->getSize();
            return c->Record({
                    {"in", c->BitIn()->Arr(inputSize)},
                    {"out", c->Out(outputType)}
                });
        });

    Generator* hydrate =
        aetherlinglib->newGeneratorDecl("hydrate", aetherlinglib->getTypeGen("hydrate_type"), hydrateParams);

    hydrate->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* outputType = c->Out(genargs.at("hydratedType")->get<Type*>());
            uint inputSize = outputType->getSize();
            // note: this gets a value for each element, so if an array has n elements, this gets
            // pushed n times
            // the string is the name of the type
            queue<tuple<Type*,string>> elementsToExamine;
            // first element to examine is hydrated output and its name relative to root
            elementsToExamine.push(make_tuple(outputType, "self.out"));
            
            walkTypeTree(def, inputSize, elementsToExamine);
        });
}
