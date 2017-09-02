#include "coreir-lib/common.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(common);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_common(Context* c) {
  Namespace* common = c->newNamespace("common");

  //Add a LUTN
  Params lutNParams({{"N",AINT}});
  common->newTypeGen("lutNType",lutNParams,[](Context* c, Args args) { 
    uint N = args.at("N")->get<ArgInt>();
    ASSERT(N<=5,"NYI due to init bit length");
    return c->Record({
      {"in",c->BitIn()->Arr(N)},
      {"out",c->Bit()}
    });
  });
  Generator* lutN = common->newGeneratorDecl("lutN",common->getTypeGen("lutNType"),lutNParams,{{"init",AINT}});
  lutN->addDefaultConfigArgs({{"init",c->argInt(0)}});
  

  Params MemGenParams = {{"width",AINT},{"depth",AINT}};
  //Linebuffer Memory. Use this for memory in linebuffer mode
  common->newTypeGen("LinebufferMemType",MemGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"valid", c->Bit()},
    });
  });
  Generator* lbMem = common->newGeneratorDecl("LinebufferMem",common->getTypeGen("LinebufferMemType"),MemGenParams);
  lbMem->addDefaultGenArgs({{"width",c->argInt(16)},{"depth",c->argInt(1024)}});
  
  //Fifo Memory. Use this for memory in Fifo mode
  common->newTypeGen("FifoMemType",MemGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"ren", c->BitIn()},
      {"almost_full", c->Bit()},
      {"valid", c->Bit()}
    });
  });
  Generator* fifoMem = common->newGeneratorDecl("FifoMem",common->getTypeGen("FifoMemType"),MemGenParams,{{"almost_full_cnt",AINT}});
  fifoMem->addDefaultGenArgs({{"width",c->argInt(16)},{"depth",c->argInt(1024)}});

  //TODO RAM

  //Linebuffer
  //Declare a TypeGenerator (in global) for linebuffer
  common->newTypeGen(
    "linebuffer_type", //name for the typegen
    {{"stencil_width",AINT},{"stencil_height",AINT},{"image_width",AINT},{"bitwidth",AINT}}, //generater parameters
    [](Context* c, Args args) { //Function to compute type
      uint stencil_width  = args.at("stencil_width")->get<ArgInt>();
      uint stencil_height  = args.at("stencil_height")->get<ArgInt>();
      //uint image_width = args.at("image_width")->get<ArgInt>();
      uint bitwidth = args.at("bitwidth")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(bitwidth)},
        {"out",c->Bit()->Arr(bitwidth)->Arr(stencil_width)->Arr(stencil_height)}
      });
    }
  );

  Generator* linebuffer = common->newGeneratorDecl(
    "Linebuffer",
    common->getTypeGen("linebuffer_type"),{
      {"stencil_width",AINT},
      {"stencil_height",AINT},
      {"image_width",AINT},
      {"bitwidth",AINT}
    }
  );
  linebuffer->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Args args) {
    uint stencil_width  = args.at("stencil_width")->get<ArgInt>();
    uint stencil_height  = args.at("stencil_height")->get<ArgInt>();
    uint image_width = args.at("image_width")->get<ArgInt>();
    uint bitwidth = args.at("bitwidth")->get<ArgInt>();
    assert((bitwidth & (bitwidth-1)) == 0); //Check if power of 2
    assert(stencil_height > 0);
    assert(stencil_width > 0);
    assert(image_width > stencil_width);
    assert(bitwidth > 0);

    Arg* aBitwidth = c->argInt(bitwidth);
    Arg* aImageWidth = c->argInt(image_width);

    // create the inital register chain
    std::string reg_prefix = "reg_";
    for (uint j = 1; j < stencil_width; ++j) {

      std::string reg_name = reg_prefix + "0_" + std::to_string(j);
      def->addInstance(reg_name, "coreir.reg", {{"width",aBitwidth}});
      
      // connect the input
      if (j == 1) {
        def->connect({"self","in"}, {reg_name, "in"});
      } else {
        std::string prev_reg = reg_prefix + "0_" + std::to_string(j-1);
        def->connect({prev_reg, "out"}, {reg_name, "in"});
      }
    }

    // connect together the memory lines
    std::string mem_prefix = "mem_";
    for (uint i = 1; i < stencil_height; ++i) {
      std::string mem_name = mem_prefix + std::to_string(i);
      def->addInstance(mem_name,"common.LinebufferMem",{{"width",aBitwidth},{"depth",aImageWidth}});

      // connect the input
      if (i == 1) {
        def->connect({"self","in"}, {mem_name, "wdata"});
      } else {
        std::string prev_mem = mem_prefix + std::to_string(i-1);
        def->connect({prev_mem, "rdata"}, {mem_name, "wdata"});
      }
    }

    // connect together the remaining stencil registers
    for (uint i = 1; i < stencil_height; ++i) {
      for (uint j = 1; j < stencil_width; ++j) {
        std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
        def->addInstance(reg_name, "coreir.reg", {{"width",aBitwidth}});
  
        // connect the input
        if (j == 1) {
          std::string mem_name = mem_prefix + std::to_string(i);
          def->connect({mem_name, "rdata"}, {reg_name, "in"});
        } else {
          std::string prev_reg = reg_prefix + std::to_string(i) + "_" + std::to_string(j-1);
          def->connect({prev_reg, "out"}, {reg_name, "in"});
        }
      }
    }

    // connect the stencil outputs
    for (uint i = 0; i < stencil_height; ++i) {
      for (uint j = 0; j < stencil_width; ++j) {
        // delays correspond to earlier pixels
        uint iflip = (stencil_height - 1) - i;
        uint jflip = (stencil_width - 1) - j;

        if (j == 0) {
          // the first column comes from input/mem
          if (i == 0) {
            def->connect({"self","in"}, {"self","out",std::to_string(iflip),std::to_string(jflip)});
          } else {
            std::string mem_name = mem_prefix + std::to_string(i);
            def->connect({mem_name, "rdata"}, {"self","out",std::to_string(iflip),std::to_string(jflip)});
          }
        } else {
          // rest come from registers
          std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
          def->connect({reg_name, "out"}, {"self","out",std::to_string(iflip),std::to_string(jflip)});
        }
      }
    }    

  });


  return common;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(common)
