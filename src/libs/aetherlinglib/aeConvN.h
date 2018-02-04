
#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <math.h>

using namespace std;
using namespace CoreIR;

void Aetherling_createConvGenerator(Context* c) {

    Namespace* aetherlinglib = c->getNamespace(AETHERLING_NAMESPACE);
    Namespace* commonlib = c->getNamespace("commonlib");
    
    Params conv1Dparams = Params({
            {"dataWidth", c->Int()},
            {"kernelWidth", c->Int()},
            {"elementWidth", c->Int()}
        });

    aetherlinglib->newTypeGen(
        "conv1D_type", // name for typegen
        conv1Dparams, // generator parameters
        [](Context* c, Values genargs) { //Function to compute type
            uint elementWidth = genargs.at("elementWidth")->get<int>();
            uint dataWidth = genargs.at("dataWidth")->get<int>();
            return c->Record({
                    {"in", c->Record({
                                {"data", c->BitIn()->Arr(elementWidth)->(dataWidth)},
                                {"kernel", c->BitIn()->Arr(elementWidth)->(kernelWidth)}
                            })},
                    {"out", c->Bit()->Arr(elementWidth)}
                });
        });

    Generator* conv1D =
        aetherlinglib->newGeneratorDecl("conv1D", aetherlinglib->getTypeGen("conv1D_type"), conv1Dparams);
   
    reduceN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
            Type* imgType = genargs.at("imgType")->get<Type*>();
            uint kernelWidth = genargs.at("kernelWidth")->get<int>();
            uint elementWidth = genargs.at("elementWidth")->get<int>();
            // create the type of that the linebuffer will kick out every clock
            // this is kernel width number of pixels (so one pixel is element width bits)
            Type* lbImgType = def->sel("self.in.data")->getType();
            ArrayType* lbInType = c->BitIn()->Arr(elementWidth);
            ArrayType* lbOutType = c->Bit()->Arr(elementWidth)->Arr(kernelWidth);
            assert(kernelWidth>0);
            assert(elementWidth>0);
            assert(dataWidth>0);
            
            // create the instances of the convolution, map, and reduce needed for conv
            // along with zip2 needed to create input to map and input ops for map and reduce

            def->addInstance("conv1DLineBuffer", "commonlib.linebuffer", {
                    {"input_type", Const::make(c, lbInType)},
                    {"output_type", Const::make(c, lbOutType)},
                    {"image_type", Const::make(c, lbImgType)},
                    {"has_valid", Const::make(c, false)},
                    {"is_last_lb", Const::make(c, true)}
                });


            def->addInstance("conv1DZip2", "aetherlinglib.zip2", {
                    {"numInputs", Const::make(c, kernelWidth)},
                    {"input0Type", Const::make(c, c->In(lbOutType))}
                    {"input1Type", Const::make(c, def->sel("self.in.kernel")->getType())}
                });

            Module* mul2Zipped = Aetherling_convert2InputModuleTo2ZippedInput(
                c, c->getModule("coreir.mul"), {{"width", Const::make(c, elementWidth)}});
            
            def->addInstance("conv1DMap", "aetherlinglib.mapN", {
                    {"parallelOperators", Const::make(c, kernelWidth)},
                    {"operator", Const::make(c, mul2Zipped)}
                });

            Module* add = c->getGenerator("coreir.add")->getModule({{"width", Const::make(c, width)}});

            def->addInstance("conv1DReduce", "aetherlinglib.reduceNSerializable", {
                    // need to multiply by 2 to get right number of layers, like 4 inputs
                    // is 3 layers and log2(8) = 3
                    {"numLayers", Const::make(c, int(log2(kernelWidth*2)))},
                    {"operator", Const::make(c, add)}
                });

            // now wire everythign up
            def->connect("self.in.data", "conv1DLineBuffer.in");
            def->connect("conv1DLineBuffer.out", "conv1DZip2.in0");
            def->connect("self.in.kernel", "conv1DZip2.in1");
            def->connect("conv1DZip2.out", "conv1DMap.in");
            def->connect("conv1DMap.out", "conv1DReduce.in");
            def->connect("conv1DReduce.out", "self.out");
        });
}
