#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <vector>
#include <math>

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(aetherlinglib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_aetherlinglib(Context* c) {

    Namespace* aetherlinglib = c->newNamespace("aetherlinglib");
    Namespace* coreirprims = c->getNamespace("coreir");


    /////////////////////////////////
    // Commonlib Types
    /////////////////////////////////

    Params widthparams = Params({{"width",c->Int()}});

    Params mapNparams = Params({
            {"width", c->Int()},
            {"N", c->Int()},
            {"numOperatorsParallel", c->Int()},
            {"cyclesPerOperation", c->Int()},
            {"operator", c->String()}
        });

    aetherlinglib->newTypeGen(
        "mapN_type", // name for typegen
        mapNparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint width = genargs.at("width")->get<int>();
            uint N = genargs.at("N")->get<int>();
            uint numOperatorsParallel = genargs.at("numOperatorsParallel")->get<int>();
            return c->Record({
                    {"in", c->BitIn()->Arr(width)->Arr(N)},
                    {"out", c->Bit()->Arr(width)->Arr(numOperatorsParallel)}
                });
        });

    aetherlinglib->newGeneratorDecl("mapN", aetherlinglib->getTypeGen("mapN_type"), mapNparams);

    addCounter(c, aetherlinglib);

    opN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint width = genargs.at("width")->get<int>();
            uint N = genargs.at("N")->get<int>();
            uint cyclesPerOperation = genargs.at("cyclesPerOperation")->get<int>();
            uint numOperatorsParallel = genargs.at("numOperatorsParallel")->get<int>();
            string op = genargs.at("operator")->get<string>();
            assert(N>0);
            assert(N >= numOperatorsParallel); // nonsensical to have more parallelism than operations

            Namespace* aetherlinglib = c->getNamespace("aetherlinglib");
            Generator* mapN = aetherlinglib->getGenerator("mapn");
            Generator* const_gen = coreirprims->getGenerator("const");

            Const* aWidth = Const::make(c,width);
            Const* aOperator = Const::make(c,op);

            uint inputsPerOperatorPreSpillover = N / numOperatorsParallel;
            uint extraInputs = N % numOperatorsParallel;
            uint maxInputsPerOperator = inputsPerOperatorPreSpillover + (extraInputs > 0 ? 1 : 0);
            Const* aMaxInputsPerOperator = Const::make(c, maxInputsPerOperator);

            vector<uint> inputsPerOperator(numOperators, inputsPerOperatorPreSpillover);

            // clock needs to be able count from when map starts doing N operations until all N
            // have been computed (for any amount of parallelism)
            uint clocksToCompleteMap = log2((inputsPerOperatorPreSpillover + 1) * cyclesPerOperation);
            def->addInstance("counterClocksPerOp", "commonlib.counter",
                             {
                                 {"width", Const::make(c, ((int) log2(cyclesPerOperation)) + 1)},
                                 {"min", Const::make(c, 0)},
                                 {"max", Const::make(c, cyclesPerOperation)},
                                 {"inc", Const::make(c, 1)}
                             });

            def->addInstance("counterWhichInput", "commonlib.counter",
                             {
                                 {"width", Const::make(c, ((int) log2(numOperatorsParallel)) + 1)},
                                 {"min", Const::make(c, 0)},
                                 {"max", Const::make(c, numOperatorsParlale)},
                                 {"inc", Const::make(c, 1)}
                             });

            
            def->addInstance("always1Const", const_gen, {{"width",Const::make(c,1)}},
                             {{"value",Const::make(c,BitVector(1,1))}});

            def->connect("always1Const.out", "counterClocksPerOp.en");
            def->connect("counterClocksPerOp.overflow", "counterWhichInput.en");

//            def->addInstance("counterWhichInput", "commonlib.counter"
            

            for (int i = 0; i < inputsPerOperator.size(); i++) {
                string idxStr = to_string(i);
                // assign the extra inputs that don't cleanly divide by the
                // number of operators 
                if (i < extraInputs) {
                    inputsPerOperator[i]++;
                }

                // for every operator, create a mux for the inputs to it, as counter goes forward,
                // mux will pass different inputs to the operator, with changes spaced enough clock
                // cycles apart that the operator can output the result to the next stage
                string muxName = "muxn" + idxStr;
                def->addInstance(muxName, "commonlib.muxn",
                                 {{"width", aWidth}, {"N", aMaxInputsPerOperator}});

                def->connect("counterWhichInput.out", muxName + ".in.sel");

                for (int j = 0; j < inputsPerOperatorPreSpillover; j++) {
                    string inputIdxStr = to_string(i*maxInputsPerOperator + j);
                    def->connect("self.in." + inputIdxStr, muxName + ".in.data." + to_string(j));
                }

                // handle spillover

                // now create the op and wire the mux into it
                def->addInstance("op_" + idxStr, op);
                string opStr = "op_" + idxStr;
                def->connect("mux.out", opStr + ".in");
                def->connect(opStr + ".out", "self.out." + to_string(j));
            }
             
            //HOW DO I HANDLE SPILLOVER? DO I GIVE A SIGNAL FOR WHEN OUT HAS CHANGED, AND A DIFFERENT ONE
            // FOR WHEN ONLY SPILLOVER HAPPENS?

        });

    return aetherlinglib;  
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(aetherlinglib)
