
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
                    {"out", c->Bit()->Arr(elementWidth)},
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
            ArrayType* kernelType = dyn_cast<ArrayType>(def->sel("self.in.kernel")->getType());
            // create the type of total image, the input per clock, and output per clock from linebuffer
            Type* lbImgType = c->BitIn()->Arr(elementWidth)->Arr(dataWidth);
            // need this to be an arr(1) as linebuffer outputs one pixel per clock (one elementwidth)
            ArrayType* lbInType = dyn_cast<ArrayType>(c->In(def->sel("self.in.data")->getType()));
            // this has to be same as kernel type as they are going to be zipped together
            // and then element-wise multiplied;
            ArrayType* lbOutType = dyn_cast<ArrayType>(c->Out(kernelType));
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

            // for zip2, note that numInputs is the size of the array of input0 and input1,
            // for input0 and 1 I just want the types of the elements, so have to strip the array lenghts
            // with getElemType
            // make 1 zip2 for each concurrent input you are processing
            /*Module* zip2PerInput = c->getGenerator("aetherlinglib.zip2")->getModule({
                    {"numInputs", Const::make(c, kernelWidth)},
                    {"input0Type", Const::make(c, c->In(lbOutType->getElemType()))}, 
                    {"input1Type", Const::make(c, c->In(kernelType->getElemType()))}
                });
            */

            Module* mul2Unzipped = c->getGenerator("coreir.mul")->
                getModule({{"width", Const::make(c, elementWidth)}});
            
            Module* mul2Zipped = Aetherling_convert2InputModuleTo2ZippedInput(c, mul2Unzipped);
            cout << 3 << endl;

            // each one of these maps processes the output associated with one input
            Module* mapForOneInput = c->getGenerator("aetherlinglib.mapParallel")->getModule({
                    {"numInputs", Const::make(c, kernelWidth)},
                    {"operator", Const::make(c, mul2Zipped)}
                });
            cout << 1 << endl;

            // now add a mapForOneInput for each input per clock
            def->addInstance("conv1DMapForAllInputs", "aetherlinglib.mapParallel", {
                    {"numInputs", Const::make(c, inputsPerClock)},
                    {"operator", Const::make(c, mapForOneInput)}
                });

            // can ignore map's ready and valid since both are fully parallel
            def->addInstance("ignoreReady", "coreir.term", {{"width", Const::make(c, 1)}});
            def->addInstance("ignoreValid", "coreir.term", {{"width", Const::make(c, 1)}});
            cout << 4 << endl;

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

            // now wire everythign up
            def->connect("self.in.data", "conv1DLineBuffer.in");
            // assuming stride is 1, so each input per clock increases the output width by 1
            for (int i = 0; i < inputsPerClock; i++) {
                cout << "hi" << endl;
                Values sliceArgs = {{"width", Const::make(c, kernelWidth + inputsPerClock - 1)},
                                    {"lo", Const::make(c,i)},
                                    {"hi", Const::make(c,kernelWidth + i)}};
                cout << "dude" << endl;
                string idx = to_string(i);
                def->addInstance("lbSlicer_" + idx, "coreir.slice", sliceArgs);
                def->connect("conv1DLineBuffer.out", "lbSlicer_" + idx + ".in");
                def->connect("lbSlicer_" + idx + ".out", "conv1DMapForAllInputs.in." + idx + ".in.el0");
                def->connect("self.in.kernel", "conv1DMapForAllInputs.in." + idx + ".in.el1");
            }
            def->connect("conv1DMap.out", "conv1DReduce.in.data");
            def->connect("conv1DMap.ready", "ignoreReady.in.0");
            def->connect("conv1DMap.valid", "ignoreValid.in.0");
            def->connect(addIdentityModule + ".out", "conv1DReduce.in.identity");
            def->connect("conv1DReduce.out", "self.out");
            def->connect("conv1DLineBuffer.valid", "self.valid");
            def->connect("self.wen", "conv1DLineBuffer.wen");
            lbInst->getModuleRef()->print();
        });
}
