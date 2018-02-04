#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <math.h>

using namespace std;
using namespace CoreIR;

string getOpName(int layer, int idxInLayer) {
    return "op_" + to_string(layer) + "_" + to_string(idxInLayer);
}

void Aetherling_createReduceGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    /*
     * parallelOperatrs - how many operators to have in parallel
     * operator - the operator to parallelize. Note that it must have two inputs known as "in0" and "in1" and 
     * one output known as "out"
     */
    Params reduceNparams = Params({
            {"numLayers", c->Int()},
            {"operator", ModuleType::make(c)}
        });

    aetherlinglib->newTypeGen(
        "reduceN_type", // name for typegen
        reduceNparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint inputs = pow(2, genargs.at("numLayers")->get<int>());
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in0")->Arr(inputs)},
                    {"out", opType->sel("out")}
                });
        });

    Generator* reduceN =
        aetherlinglib->newGeneratorDecl("reduceN", aetherlinglib->getTypeGen("reduceN_type"), reduceNparams);

    reduceN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numLayers = genargs.at("numLayers")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            assert(numLayers>0);

            // create each layer
            for (uint i = 0; i < numLayers; i++) {
                // since its a binary tree, each layer has 2^i elements
                for (uint j = 0; j < pow(2, i); j++) {
                    string opStr = getOpName(i, j);
                    def->addInstance(opStr, opModule);
                    // wire up inputs special only if first layer
                    if (i == numLayers - 1) {
                        def->connect("self.in." + to_string(j*2), opStr + ".in0");
                        def->connect("self.in." + to_string(j*2+1), opStr + ".in1");
                    }
                    // wire output special only if last layer
                    if (i == 0) {
                        def->connect(opStr + ".out", "self.out");
                    }
                    else {
                        def->connect(opStr + ".out", getOpName(i-1, j/2) + ".in" + to_string(j % 2));
                    }
                }
            }
        });

    aetherlinglib->newTypeGen(
        "reduceNSerializable_type", // name for typegen
        reduceNparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint inputs = pow(2, genargs.at("numLayers")->get<int>());
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            return c->Record({
                    {"in", opType->sel("in0")->Arr(inputs)},
                    {"out", opType->sel("out")},
                    {"mergeCur", c->BitIn()} // set this bit if you want the current output to be merged with
                    // the last one
                });
        });

    Generator* reduceNSerializable =
        aetherlinglib->newGeneratorDecl(
            "reduceNSerializable",
            aetherlinglib->getTypeGen("reduceNSerializable_type"),
            reduceNparams);

    reduceNSerializable->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint numLayers = genargs.at("numLayers")->get<int>();
            Module* opModule = genargs.at("operator")->get<Module*>();
            RecordType* opType = opModule->getType();
            assert(numLayers>0);

            def->addInstance("reducer", "aetherlinglib.reduceN", genargs);
            def->connect("self.in", "reducer.in");

            // have a mux to switch between merged and unmerged outputs
            def->addInstance("mergeMux", "commonlib.muxn",
                             {{"width", Const::make(c, opType->sel("in0")->getSize())}, {"N", Const::make(c, 2)}});
            // connect the current output directly to the merge
            def->connect("reducer.out", "mergeMux.in.data.0");
            // also merge the current output with the last one
            def->addInstance("mergeOp", opModule);
            opType->print();
            def->addInstance("lastOutputReg", "coreir.reg", {{"width", Const::make(c, opType->sel("out")->getSize())}});
            def->connect("reducer.out", "mergeOp.in0");
            def->connect("lastOutputReg.out", "mergeOp.in1");
            def->connect("mergeOp.out", "mergeMux.in.data.1");
            // pass the current chosen ouptut (merged or unmerged) to out and back to reg so that reg
            // can repeat over multiple passes if necessary
            def->connect("self.mergeCur", "mergeMux.in.sel.0");
            def->connect("mergeMux.out", "lastOutputReg.in");
            def->connect("mergeMux.out", "self.out");
        });    
            
}
