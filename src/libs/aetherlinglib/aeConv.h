
#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <math.h>

using namespace std;
using namespace CoreIR;

void Aetherling_createConvGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    Params conv1Dparams = Params({
            {"dataWidth", c->Int()},
            {"inputsPerClock", c->Int()},
            {"kernelWidth", c->Int()},
            {"elementWidth", c->Int()}
        });

    aetherlinglib->newTypeGen(
        "conv1D_type", // name for typegen
        conv1Dparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint elementWidth = genargs.at("elementWidth")->get<int>();
            uint kernelWidth = genargs.at("kernelWidth")->get<int>();
            uint inputsPerClock = genargs.at("inputsPerClock")->get<int>();
            return c->Record({
                    {"in", c->Record({
                                {"data", c->BitIn()->Arr(elementWidth)->Arr(inputsPerClock)},
                                {"kernel", c->BitIn()->Arr(elementWidth)->Arr(kernelWidth)}
                            })},
                    {"wen", c->BitIn()},
                    {"out", c->Bit()->Arr(elementWidth)->Arr(inputsPerClock)},
                    {"valid", c->Bit()}
                });
        });

    Generator* conv1D =
        aetherlinglib->newGeneratorDecl("conv1D", aetherlinglib->getTypeGen("conv1D_type"), conv1Dparams);
   
    conv1D->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            uint kernelWidth = genargs.at("kernelWidth")->get<int>();
            uint elementWidth = genargs.at("elementWidth")->get<int>();
            uint dataWidth = genargs.at("dataWidth")->get<int>();
            uint inputsPerClock = genargs.at("inputsPerClock")->get<int>();
            // create the type of total image, the input per clock, and output per clock from linebuffer
            Type* lbImgType = c->BitIn()->Arr(elementWidth)->Arr(dataWidth);
            // need this to be an arr(1) as linebuffer outputs one pixel per clock (one elementwidth)
            ArrayType* lbInType = dyn_cast<ArrayType>(c->In(def->sel("self.in.data")->getType()));
            // this is kernel width plus 1 for each extra input after the first one per clock
            ArrayType* lbOutType = dyn_cast<ArrayType>(c->Bit()->Arr(elementWidth)->
                                                       Arr(kernelWidth + inputsPerClock - 1));
            assert(kernelWidth>0);
            assert(elementWidth>0);

            // create the instances of the convolution, map, and reduce needed for conv
            // along with zip2 needed to create input to map and input ops for map and reduce
            Instance* lbInst = def->addInstance("conv1DLineBuffer", "commonlib.linebuffer", {
                    {"input_type", Const::make(c, lbInType)},
                    {"output_type", Const::make(c, lbOutType)},
                    {"image_type", Const::make(c, lbImgType)},
                    {"has_valid", Const::make(c, true)}
                });

            def->addInstance("overlapPartition", "aetherlinglib.overlapPartition", {
                    {"elementType", Const::make(c, lbOutType->getElemType())},
                    {"numOverlapped", Const::make(c, inputsPerClock)},
                    {"arrayLen", Const::make(c, kernelWidth)}
                });

            Module* mul2Unzipped = c->getGenerator("coreir.mul")->
                getModule({{"width", Const::make(c, elementWidth)}});
            
            // each one of these maps processes the output associated with one input
            Module* mapForOneInput = c->getGenerator("aetherlinglib.mapParallel")->getModule({
                    {"numInputs", Const::make(c, kernelWidth)},
                    {"operator", Const::make(c, mul2Unzipped)}
                });

            // now add a mapForOneInput for each input per clock
            def->addInstance("conv1DMapForAllInputs", "aetherlinglib.mapParallel", {
                    {"numInputs", Const::make(c, inputsPerClock)},
                    {"operator", Const::make(c, mapForOneInput)}
                });

            Module* add = c->getGenerator("coreir.add")->getModule({{"width", Const::make(c, elementWidth)}});
            string addIdentityModule = Aetherling_addCoreIRConstantModule(c, def, elementWidth, Const::make(c, elementWidth, 0));

            // each reduce handles the output associated with each input per clock
            Module* reduceForOneInput = c->getGenerator("aetherlinglib.reduceParallel")->getModule({
                    {"numInputs", Const::make(c, kernelWidth)},
                    {"operator", Const::make(c, add)}
                });

            // now add a reduceForOneInput for input for clock
            def->addInstance("conv1DReduceForAllInputs", "aetherlinglib.mapParallel", {
                    {"numInputs", Const::make(c, inputsPerClock)},
                    {"operator", Const::make(c, reduceForOneInput)}
                });

            // now wire everything up
            def->connect("self.in.data", "conv1DLineBuffer.in");
            // assuming stride is 1, so each input per clock increases the output width by 1
            def->connect("conv1DLineBuffer.out", "overlapPartition.in");
            def->connect("overlapPartition.out", "conv1DMapForAllInputs.in0");
            // connect the kernel to every in1
            for (uint i = 0; i < inputsPerClock; i++) {
                string idx = to_string(i);
                def->connect("self.in.kernel", "conv1DMapForAllInputs.in1." + idx);
                def->connect("conv1DMapForAllInputs.out." + idx,
                             "conv1DReduceForAllInputs.in." + idx + ".data");
                def->connect(addIdentityModule + ".out", "conv1DReduceForAllInputs.in." + idx + ".identity");
            }
            def->connect("conv1DReduceForAllInputs.out", "self.out");
            def->connect("conv1DLineBuffer.valid", "self.valid");
            def->connect("self.wen", "conv1DLineBuffer.wen");
            lbInst->getModuleRef()->print();
        });
}
