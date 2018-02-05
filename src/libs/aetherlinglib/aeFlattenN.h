#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <stdio.h>

using namespace std;
using namespace CoreIR;

void Aetherling_createFlattenGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * inputType - the type that you want to flatten
     * outputType - what you want to flatten it into, inputType must be some set of arrays of this
     */
    Params flattenNparams = Params({
            {"inputType", CoreIRType::make(c)},
            {"singleElementOutputType", CoreIRType::make(c)}
        });

    aetherlinglib->newTypeGen(
        "flattenN_type", // name for typegen
        flattenNparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint outputSize = 1;
            // increment this for each dimension that must be flattened by
            Type* inputType = genargs.at("inputType")->get<Type*>();
            Type* singleElementOutputType = genargs.at("singleElementOutputType")->get<Type*>();
            // strip off dimensions until you get to the type equal to the one to output
            for (
                // must do this cast later as curType may not always be an arrayType
                Type* curType = inputType, ArrayType* curAsArray;
                curType != outputTypesingleElementOutputType;
                curType = curAsArray->getElemType()) {
                // If this cast fails, its probably because inputType wasn't an array of singleElementOutputType
                curAsArray = dynamic_cast<ArrayType*>(curType);
                outputSize *= curAsArray->getLen();
            }
            return c->Record({
                    {"in", inputType},
                    {"out", singleElementOutputType->Arr(outputSize)}
                });
        });

    Generator* flattenN =
        aetherlinglib->newGeneratorDecl("flattenN", aetherlinglib->getTypeGen("flattenN_type"), flattenNparams);

    flattenN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            ArrayType* inputType = dyn_cast<ArrayType>(genargs.at("inputType")->get<Type*>());
            ArrayType* outputType = dyn_cast<ArrayType>(def->sel("self.out")->getType());
            // recursion:
            // base case: the input type is same as the full output type (array, not single element)
            // in this case, just iterate through all the inputs and flatten them
            if (outputType == inputType) {
                for (uint i = 0; i < inputType->getLen(); i++) {
                    string iStr = to_string(i);
                    def->connect("self.in." + i, "self.out." + i);
                }
            }
            // recursion case:
            // for each element in top level array of the inputType, create a flattener and
            // then wire each of its outputs to this flattener's output
            else {
                uint inputTypeLen = inputType->getLen();
                for (uint i = 0; i < inputTypeLen; i++) {
                    string iStr = to_string(i);
                    def->addInstance("flattenNInner_" + iStr, flattenN, {
                            {"inputType", inputType->getElemType()},
                            {"singleElementOutputType", genargs.at("singleElementOutputType")->get<Type*>()}
                        });
                    def->connect("self.in." + iStr, "flattenNInner_" + iStr + ".in");
                    // wire up each output from the inner to the output
                    for (uint j = 0; j < ; j++) {
                        string jStr = to_string(j);
                        string outIdxStr = to_string(i*inputTypeLen + j)
                            def->connect("flattenNInner_" + iStr + ".out." + jStr, "self.out." + outIdxStr);
                    }
                    def->connect("flattenNInner_" + idxStr + ".in");
                    // def->connect("self.out."
                    def->connect("self.in1." + idxStr, "self.out." + idxStr + ".el1");
                }
            }
        });
}

uint getFlattenedSize(Type* containerType, Type* innerType) {
    uint flattenedSize = 1;
    for (
        // must do this cast later as curType may not always be an arrayType
        Type* curType = containerType, ArrayType* curAsArray;
        curType != innerType;
        curType = curAsArray->getElemType()) {
        // If this cast fails, its probably because containerType wasn't an array (to some degree) of innerType
        curAsArray = dynamic_cast<ArrayType*>(curType);
        flattenedSize *= curAsArray->getLen();
    }
    return flattenedSize;
}

        
