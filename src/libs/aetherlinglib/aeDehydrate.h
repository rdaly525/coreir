#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>
#include <iostream>
#include <queue>
#include <tuple>

using namespace std;
using namespace CoreIR;

//void wireInputsOrOutputs

/* Dehydrate converts a nested structure into an array of bits that can be passed to muxes, serializers,
 * and other objects that can't handle complex types 
 * Note: unlike flatten, don't need get size as all types already have a getsize that gives number of bits
 */

void Aetherling_createHydrateAndDehydrateGenerators(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    /*
     * inputType - the type that you want to dehydrate into just bits
     */
    Params dehydateParams = Params({
            {"inputType", CoreIRType::make(c)}
        });

    aetherlinglib->newTypeGen(
        "dehydrate_type", // name for typegen
        dehydrateParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            Type* inputType = genargs.at("inputType")->get<Type*>();
            uint outputSize = inputType->getSize();
            return c->Record({
                    {"in", inputType},
                    {"out", c->Bit->Arr(outputSize)}
                });
        });

    Generator* dehydrate =
        aetherlinglib->newGeneratorDecl("dehydrate", aetherlinglib->getTypeGen("dehydrate_type"), dehydrateParams);

    dehydrate->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* inputType = c->In(genargs.at("inputType")->get<Type*>());
            uint outputSize = inputType->getSize();
            // note: this gets a value for each element, so if an array has n elements, this gets
            // pushed n times
            // the string is the name of the type
            queue<tuple<Type*,string>> elementsToExamine;
            elementsToExamine.push(make_tuple(inputType, "self.in"));

            // go through every type
            for (int curOutput = 0; !elementsToExamine.empty(); curOutput++) {
                // get the next type and its name
                auto curElement = elementsToExamine.pop();
                Type* curType = get<0>(curElement);
                string curName = get<1>(curElement);

                // add its children elements to the queue if its not a bit, or wire up the bits
                switch(curType->getKind()) {
                case TK_Bit :
                    ASSERT(0, "Can't happen case as inputType has been made all BitIn");
                case TK_BitIn :
                    def->connect(curName, "self.out." + to_string(curOutput));
                    break;
                case TK_Array :
                    Type* curAsArr = dyn_cast<ArrayType>(def->sel("self.out")->getType());
                    Type* elemType = curAsArr->getElemType();
                    for (int i = 0; i < curAsArr->getLen(); i++) {
                        elementsToExamine.push(make_tuple(elemType, curName + "." + to_string(i)));
                    }
                    break;
                case TK_Record :
                    Type* curAsRec = dyn_cast<RecordType>(def->sel("self.out")->getType());
                    auto nameTypeMap = curAsRec->getRecord();
                    for (auto it = nameTypeMap.begin(); it != nameTypeMap.end(); ++it) {
                        elementsToExamine.push(make_tuple(it->second, curName + "." + it->first));
                    }
                    break;
                case TK_Named :
                    Type* curAsNamed = dyn_cast<NamedType>(def->sel("self.out")->getType());
                    elementsToExamine.push(make_tuple(curAsNamed->getRaw(), curName));
                default : ASSERT(0, "dehydrating invalid type " + inputType->toString());
                }
            }
        });
}
