#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>
#include <iostream>

using namespace std;
using namespace CoreIR;

void Aetherling_createOverlapPartitionGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    /*
     * elementType - the type in each array
     * numOverlapped - how many arrays are overlapped in the input, each array offset 1 from the next
     * arrayLen - how long is one array
     */
    Params overlapPartitionParams = Params({
            {"elementType", CoreIRType::make(c)},
            {"numOverlapped", c->Int()},
            {"arrayLen", c->Int()}
        });

    aetherlinglib->newTypeGen(
        "overlapPartition_type", // name for typegen
        overlapPartitionParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            Type* elementType = genargs.at("elementType")->get<Type*>();
            uint numOverlapped = genargs.at("numOverlapped")->get<int>();
            uint arrayLen = genargs.at("arrayLen")->get<int>();
            return c->Record({
                    {"in", c->In(elementType->Arr(arrayLen + numOverlapped - 1))},
                    {"out", c->Out(elementType->Arr(arrayLen)->Arr(numOverlapped))}
                });
        });

    Generator* overlapPartition =
        aetherlinglib->newGeneratorDecl("overlapPartition", aetherlinglib->getTypeGen("overlapPartition_type"),
                                        overlapPartitionParams);

    overlapPartition->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numOverlapped = genargs.at("numOverlapped")->get<int>();
            uint arrayLen = genargs.at("arrayLen")->get<int>();

            // for each overlapping array
            for (uint i = 0; i < numOverlapped; i++) {
                // for each element in that array
                for (uint j = 0; j < arrayLen; j++) {
                    def->connect("self.in." + to_string(i+j), "self.out." + to_string(i) + "." + to_string(j));
                }
            }
        });
}
