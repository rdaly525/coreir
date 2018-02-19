
#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <math.h>

using namespace std;
using namespace CoreIR;

void Aetherling_createConvGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    
    Params conv1Dparams = Params({
            {"dataWidth", c->Int()},
            {"inputPerClockWidth", c->Int()},
            {"kernelWidth", c->Int()},
            {"elementWidth", c->Int()}
        });

    aetherlinglib->newTypeGen(
        "conv1D_type", // name for typegen
        conv1Dparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint elementWidth = genargs.at("elementWidth")->get<int>();
            uint kernelWidth = genargs.at("kernelWidth")->get<int>();
            uint inputPerClockWidth = genargs.at("inputPerClockWidth")->get<int>();
            return c->Record({
                    {"in", c->Record({
                                {"data", c->BitIn()->Arr(elementWidth)->Arr(inputPerClockWidth)},
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
            def->addInstance("conv1DZip2", "aetherlinglib.zip2", {
                    {"numInputs", Const::make(c, kernelWidth)},
                    {"input0Type", Const::make(c, c->In(lbOutType->getElemType()))}, 
                    {"input1Type", Const::make(c, c->In(kernelType->getElemType()))}
                });

            Module* mul2Unzipped = c->getGenerator("coreir.mul")->
                getModule({{"width", Const::make(c, elementWidth)}});

            
            Module* mul2Zipped = Aetherling_convert2InputModuleTo2ZippedInput(c, mul2Unzipped);
            
            def->addInstance("conv1DMap", "aetherlinglib.mapN", {
                    {"parallelOperators", Const::make(c, kernelWidth)},
                    {"operator", Const::make(c, mul2Zipped)}
                });

            Module* add = c->getGenerator("coreir.add")->getModule({{"width", Const::make(c, elementWidth)}});
            string addIdentityModule = Aetherling_addCoreIRConstantModule(c, def, elementWidth, Const::make(c, elementWidth, 0));

            def->addInstance("conv1DReduce", "aetherlinglib.reduceNAnyInputs", {
                    // need to multiply by 2 to get right number of layers, like 4 inputs
                    // is 3 layers and log2(8) = 3
                    {"numInputs", Const::make(c, kernelWidth)},
                    {"operator", Const::make(c, add)}
                });

            // now wire everythign up
            def->connect("self.in.data", "conv1DLineBuffer.in");
            def->connect("conv1DLineBuffer.out", "conv1DZip2.in0");
            def->connect("self.in.kernel", "conv1DZip2.in1");
            def->connect("conv1DZip2.out", "conv1DMap.in");
            def->connect("conv1DMap.out", "conv1DReduce.in.data");
            def->connect(addIdentityModule + ".out", "conv1DReduce.in.identity");
            def->connect("conv1DReduce.out", "self.out");
            def->connect("conv1DLineBuffer.valid", "self.valid");
            def->connect("self.wen", "conv1DLineBuffer.wen");
            lbInst->getModuleRef()->print();
        });
}
