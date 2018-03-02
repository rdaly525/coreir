#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <string.h>
#include <stdio.h>
#include <vector>

using namespace std;
using namespace CoreIR;

vector<pair<string,Type*>> getInputOrOutputFields(Context* c, RecordType* rtype, bool getInputs) {
    auto fields = rtype->getRecord();
    vector<pair<string, Type*>> returnFields;
    for (auto& field : fields) {
        // since all input ops to map should be single cycle, don't deal with this.
        if (field.first == "ready" || field.first == "valid") {
            continue;
        }
        else if (field.second->isInput() && getInputs) {
            returnFields.push_back(field);
        }
        else if (field.second->isOutput() && !getInputs) {
            returnFields.push_back(field);
        }
        else if (field.second->isMixed()) {
            ASSERT(0, "Can't map over field " + field.first + " with mixed type");
        }
    }
    return returnFields;
}

Type* generateMapType(Context* c, Values genargs, bool sequential) {
    uint numInputs = genargs.at("numInputs")->get<int>();
    Module* opModule = genargs.at("operator")->get<Module*>();
    RecordType* opType = opModule->getType();
    auto opInputFields = getInputOrOutputFields(c, opType, true);
    auto opOutputFields = getInputOrOutputFields(c, opType, false);
    RecordType* mapPorts = c->Record({});
    for (auto opInputField : opInputFields) {
        mapPorts = mapPorts->appendField(opInputField.first, opInputField.second->Arr(numInputs));
    }
    for (auto opOutputField : opOutputFields) {
        mapPorts = mapPorts->appendField(opOutputField.first, opOutputField.second->Arr(numInputs));
    }
    if (sequential) {
        mapPorts = mapPorts->appendField("ready", c->Bit());
        mapPorts = mapPorts->appendField("valid", c->Bit());
    }
    return mapPorts;
}

void Aetherling_createMapGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * This type is for all maps, from fully sequential to fully parallel
     * parallelOperatrs - how many operators to have in parallel
     * operator - the operator to parallelize. Note that it must have one input known as "in" and 
     * one output known as "out"
     */
    Params mapSeqParParams = Params({
            {"numInputs", c->Int()},
            {"operator", ModuleType::make(c)},
        });

    aetherlinglib->newTypeGen(
        "mapPar_type", // name for typegen
        mapSeqParParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            return generateMapType(c, genargs, false);
        });

    Generator* mapParallel =
        aetherlinglib->newGeneratorDecl("mapParallel", aetherlinglib->getTypeGen("mapPar_type"), mapSeqParParams);

    mapParallel->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            auto opInputFields = getInputOrOutputFields(c, opType, true);
            auto opOutputFields = getInputOrOutputFields(c, opType, false);

            // now create each op and wire the inputs and outputs to it
            for (uint i = 0; i < numInputs; i++) {
                string idxStr = to_string(i);                
                string opStr = "op_" + idxStr;
                def->addInstance(opStr, opModule);
                for (auto opInputField : opInputFields) {
                    def->connect("self." + opInputField.first + "." + idxStr, opStr + "." + opInputField.first);
                }
                for (auto opOutputField: opOutputFields) {
                    def->connect(opStr + "." + opOutputField.first, "self." + opOutputField.first + "." + idxStr);
                }
            }
            /*
            string oneConst;
            // if op has ready or valid, wire those up to this map's ready and valid
            // create a one output if this map needs to drive either its own ready or valid
            cout << "as" << endl;
            bool hasReady = opModule->getType()->canSel("ready");
            bool hasValid = opModule->getType()->canSel("valid");
            cout << "a" << endl;
            if (!hasReady || !hasValid) {
                oneConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            }
            // all ops should be same, so can take ready and valid from first op
            if (hasReady) {
                def->connect("op_0.ready", "self.ready");
            }
            else {
                def->connect(oneConst + ".out.0", "self.ready");
            }
            cout << "b" << endl;
            if (hasValid) {
                def->connect("op_0.valid", "self.valid");
            }
            else {
                def->connect(oneConst + ".out.0", "self.valid");
            }
            */
        });

    aetherlinglib->newTypeGen(
        "mapSeq_type", // name for typegen
        mapSeqParParams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            return generateMapType(c, genargs, true);
        });
    /* 
     * This implementation of map is fully sequential, takes entire input in first cycle, emits it all
     * on last cycle
     */
    Generator* mapSequential =
        aetherlinglib->newGeneratorDecl("mapSequential", aetherlinglib->getTypeGen("mapSeq_type"), mapSeqParParams);

    mapSequential->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numInputs = genargs.at("numInputs")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            auto opInputFields = getInputOrOutputFields(c, opType, true);
            auto opOutputFields = getInputOrOutputFields(c, opType, false);

            def->addInstance("op", opModule);
            string enableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 1));
            string disableConst = Aetherling_addCoreIRConstantModule(c, def, 1, Const::make(c, 1, 0));
            // create a streamify for each input and wire each streamify to its op input
            for (auto opInputField : opInputFields) {
                Values streamifyParams({
                    {"elementType", Const::make(c, opInputField.second)},
                    {"arrayLength", Const::make(c, numInputs)}
                });
                string streamifyName = "streamify_" + opInputField.first;
                def->addInstance(streamifyName, "aetherlinglib.streamify", streamifyParams);
                def->connect("self." + opInputField.first, streamifyName + ".in");
                def->connect(streamifyName + ".out", "op." + opInputField.first);
                // enable and prevent reset of all streamifies
                def->connect(enableConst + ".out.0", streamifyName + ".en");
                def->connect(disableConst + ".out.0", streamifyName + ".reset");
                // ignore the readys from all the streamifies, will take one later
                def->addInstance("ignoreReady" + streamifyName, "coreir.term",
                                 {{"width", Const::make(c, 1)}});
                def->connect(streamifyName + ".ready", "ignoreReady" + streamifyName + ".in.0");
            }
            for (auto opOutputField: opOutputFields) {
                Values arrayifyParams({
                    {"elementType", Const::make(c, opOutputField.second)},
                    {"arrayLength", Const::make(c, numInputs)}
                });
                string arrayifyName = "arrayify_" + opOutputField.first;
                def->addInstance(arrayifyName, "aetherlinglib.arrayify", arrayifyParams);
                def->connect("op." + opOutputField.first, arrayifyName + ".in");
                def->connect(arrayifyName + ".out", "self." + opOutputField.first);
                // enable and prevent reset of all streamifies
                def->connect(enableConst + ".out.0", arrayifyName + ".en");
                def->connect(disableConst + ".out.0", arrayifyName + ".reset");
                // ignore the readys from all the streamifies, will take one later
                def->addInstance("ignoreValid" + arrayifyName, "coreir.term",
                                 {{"width", Const::make(c, 1)}});
                def->connect(arrayifyName + ".valid", "ignoreValid" + arrayifyName + ".in.0");

            }

            // handle the ready and valid from one streamify and arrayify
            def->connect("streamify_" + opInputFields.front().first + ".ready", "self.ready");
            def->connect("arrayify_" + opOutputFields.front().first + ".valid", "self.valid");
        });
}
