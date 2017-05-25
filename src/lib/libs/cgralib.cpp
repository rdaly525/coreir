#include "coreir-lib/cgralib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(cgralib);

using namespace CoreIR;

Namespace* CoreIRLoadLibrary_cgralib(Context* c) {
  
  Namespace* cgralib = c->newNamespace("cgralib");
  
  //Unary op declaration
  Params widthParams = {{"width",AINT}};
  cgralib->newTypeGen("UnaryType",widthParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"in",c->BitIn()->Arr(width)},
      {"out",c->Bit()->Arr(width)},
    });
  });

  //PE declaration
  Params PEGenParams = {{"width",AINT},{"numin",AINT}};
  Params opParams = {{"op",ASTRING}};
  cgralib->newTypeGen("PEType",PEGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint numin = args.at("numin")->get<ArgInt>();
    return c->Record({
      {"data",c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(numin)},
        {"out",c->Bit()->Arr(width)}
      })},
      {"bit",c->Record({
        {"in",c->BitIn()->Arr(numin)},
        {"out",c->Bit()}
      })}
    });
  });
  cgralib->newGeneratorDecl("PE",cgralib->getTypeGen("PEType"),PEGenParams,opParams);

  //Const Declaration
  Params valueParams = {{"value",AINT}};
  cgralib->newTypeGen("SrcType",widthParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"out",c->Bit()->Arr(width)}
    });
  });
  cgralib->newGeneratorDecl("Const",cgralib->getTypeGen("SrcType"),widthParams,valueParams);

  //Reg declaration
  cgralib->newGeneratorDecl("Reg",cgralib->getTypeGen("UnaryType"),widthParams);

  //IO Declaration
  Params modeParams = {{"mode",ASTRING}};
  cgralib->newGeneratorDecl("IO",cgralib->getTypeGen("UnaryType"),widthParams,modeParams);

  //Mem declaration
  Params MemGenParams = {{"width",AINT},{"depth",AINT}};
  cgralib->newTypeGen("MemType",MemGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"addr", c->BitIn()->Arr(width)},
      {"rdata", c->Bit()->Arr(width)},
      {"ren", c->BitIn()},
      {"empty", c->Bit()},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"full", c->Bit()}
    });
  });
  cgralib->newGeneratorDecl("Mem",cgralib->getTypeGen("MemType"),MemGenParams,modeParams);

  //Declare a TypeGenerator (in global) for linebuffer
  cgralib->newTypeGen(
    "linebuffer_type", //name for the typegen
    {{"stencil_width",AINT},{"stencil_height",AINT},{"image_width",AINT},{"bitwidth",AINT}}, //generater parameters
    [](Context* c, Args args) { //Function to compute type
      uint stencil_width  = args.at("stencil_width")->get<ArgInt>();
      uint stencil_height  = args.at("stencil_height")->get<ArgInt>();
      //uint image_width = args.at("image_width")->get<ArgInt>();
      uint bitwidth = args.at("bitwidth")->get<ArgInt>();
      return c->Record({
	  {"in",c->BitIn()->Arr(bitwidth)},
	  {"out",c->Bit()->Arr(bitwidth)->Arr(stencil_height)->Arr(stencil_width)}
      });
    }
  );


  Generator* linebuffer = cgralib->newGeneratorDecl("Linebuffer",
					      cgralib->getTypeGen("linebuffer_type"),
					      {{"stencil_width",AINT},{"stencil_height",AINT},
					       {"image_width",AINT},{"bitwidth",AINT}});
  
  linebuffer->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Args args) {
    uint stencil_width  = args.at("stencil_width")->get<ArgInt>();
    uint stencil_height  = args.at("stencil_height")->get<ArgInt>();
    uint image_width = args.at("image_width")->get<ArgInt>();
    uint bitwidth = args.at("bitwidth")->get<ArgInt>();
    assert((bitwidth & (bitwidth-1)) == 0); //Check if power of 2
    assert(stencil_height > 1);
    assert(stencil_width > 0);
    assert(image_width > stencil_width);
    assert(bitwidth > 0);

    Namespace* cgralib = CoreIRLoadLibrary_cgralib(c);
    Generator* Mem = cgralib->getGenerator("Mem");
    Generator* Reg = cgralib->getGenerator("Reg");
    Arg* aBitwidth = c->argInt(bitwidth);
    Arg* aImageWidth = c->argInt(image_width);

    // create the inital register chain
    std::string reg_prefix = "reg_";
    for (uint j = 0; j < stencil_width; ++j) {

      std::string reg_name = reg_prefix + "0_" + std::to_string(j);
      def->addInstance(reg_name, Reg, {{"width",aBitwidth}});
      
      // connect the input
      if (j == 0) {
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
      def->addInstance(mem_name,Mem,{{"width",aBitwidth},{"depth",aImageWidth}},{{"mode",c->argString("o")}});

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
      for (uint j = 0; j < stencil_width; ++j) {
	std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
	def->addInstance(reg_name, Reg, {{"width",aBitwidth}});
	
	// connect the input
	if (j == 0) {
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
	std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
	def->connect({reg_name, "out"}, {"self","out",std::to_string(i),std::to_string(j)});
      }
    }    

  });

  return cgralib;
}
