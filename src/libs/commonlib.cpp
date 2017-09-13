#include "coreir/libs/commonlib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(commonlib);

using namespace std;
using namespace CoreIR;

uint num_bits(uint N) {
  uint num_shifts = 0;
  uint temp_value = N;
  while (temp_value > 0) {
    temp_value  = temp_value >> 1;
    num_shifts++;
  }
  return num_shifts;
}

Namespace* CoreIRLoadLibrary_commonlib(Context* c) {
  
  Namespace* commonlib = c->newNamespace("commonlib");
  Namespace* coreirprims = c->getNamespace("coreir");
 
  /////////////////////////////////
  // Commonlib Types
  /////////////////////////////////
  
  Params widthparams = Params({{"width",AINT}});
  // TypeGens defined in coreirprims

  //muxN type
  commonlib->newTypeGen(
    "muxN_type", //name for the typegen
    {{"width",AINT},{"N",AINT}}, //generater parameters
    [](Context* c, Args args) { //Function to compute type
      uint width = args.at("width")->get<ArgInt>();
      uint N = args.at("N")->get<ArgInt>();
      return c->Record({
        {"in",c->Record({
              {"data",c->BitIn()->Arr(width)->Arr(N)},
              {"sel",c->BitIn()->Arr(width)}
            })},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

  //opN type
  commonlib->newTypeGen(
    "opN_type", //name for the typegen
    {{"width",AINT},{"N",AINT},{"operator",ASTRING}}, //generater parameters
    [](Context* c, Args args) { //Function to compute type
      uint width = args.at("width")->get<ArgInt>();
      uint N = args.at("N")->get<ArgInt>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(N)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );


  /////////////////////////////////
  // Commonlib Arithmetic primitives
  //   umin,smin,umax,smax
  /////////////////////////////////

  //Lazy way:
  unordered_map<string,vector<string>> opmap({
    {"binary",{
     "umin","smin","umax","smax"
    }},
  });
  
  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = coreirprims->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      commonlib->newGeneratorDecl(op,tg,widthparams);
    }
  }

  /////////////////////////////////
  // definition of not equal     //
  /////////////////////////////////
  Generator* notEqual = commonlib->newGeneratorDecl("neq",coreirprims->getTypeGen("binaryReduce"),{{"width",AINT}});

  notEqual->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();

    Namespace* coreirprims = c->getNamespace("coreir");
    Generator* equal = coreirprims->getGenerator("eq");
    Generator* logicalNot = coreirprims->getGenerator("not");
    
    // create necessary hardware
    Arg* aWidth = c->argInt(width);
    def->addInstance("equal",equal,{{"width",aWidth}});
    def->addInstance("not",logicalNot,{{"width",c->argInt(1)}});

    // connect hardware
    def->connect("self.in0","equal.in0");
    def->connect("self.in1","equal.in1");
    def->connect("equal.out","not.in");
    def->connect("not.out","self.out");

  });

  /////////////////////////////////
  // muxN definition             //
  /////////////////////////////////

  Generator* muxN = commonlib->newGeneratorDecl("muxn",commonlib->getTypeGen("muxN_type"),{{"width",AINT},{"N",AINT}});
  
  muxN->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint N = args.at("N")->get<ArgInt>();
    assert(N>0);

    Namespace* stdlib = c->getNamespace("coreir");
    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* mux2 = stdlib->getGenerator("mux");
    Generator* passthrough = stdlib->getGenerator("passthrough");
    Generator* muxN = commonlib->getGenerator("muxn");
    
    Arg* aWidth = c->argInt(width);
    
    if (N == 1) {
      def->addInstance("passthrough",passthrough,{{"type",c->argType(c->BitIn()->Arr(width))}});
    }
    else if (N == 2) {
      def->addInstance("join",mux2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      def->connect("self.in.data.0","join.in0");
      def->connect("self.in.data.1","join.in1");
      def->connect("self.in.sel.0", "join.sel");
    }
    else {
      def->addInstance("join",mux2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      //Connect half instances
      uint Nbits = num_bits(N-1); // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits-1);
      uint Nsmallhalf = N - Nlargehalf;
      def->connect({"self","in","sel",to_string(Nbits-1)},{"join","sel"});

      cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking into " << Nlargehalf << " and " << Nsmallhalf <<endl;
      Arg* aNlarge = c->argInt(Nlargehalf);
      Arg* aNsmall = c->argInt(Nsmallhalf);

      def->addInstance("muxN_0",muxN,{{"width",aWidth},{"N",aNlarge}});
      def->addInstance("muxN_1",muxN,{{"width",aWidth},{"N",aNsmall}});
      for (uint i=0; i<Nlargehalf; ++i) {
        def->connect({"self","in","data",to_string(i)},{"muxN_0","in","data",to_string(i)});
      }
      for (uint i=0; i<Nsmallhalf; ++i) {
        def->connect({"self","in","data",to_string(i+Nlargehalf)},{"muxN_1","in","data",to_string(i)});
      }
      def->connect("muxN_0.out","join.in0");
      def->connect("muxN_1.out","join.in1");
    }

  });

  /////////////////////////////////
  // opN definition             //
  /////////////////////////////////

  Generator* opN = commonlib->newGeneratorDecl("opn",commonlib->getTypeGen("opN_type"),{{"width",AINT},{"N",AINT},{"operator",ASTRING}});
  
  opN->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    uint N = args.at("N")->get<ArgInt>();
    std::string op2 = args.at("operator")->get<ArgString>();
    assert(N>0);

    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* opN = commonlib->getGenerator("opn");
    
    Arg* aWidth = c->argInt(width);
    Arg* aOperator = c->argString(op2);
    
    if (N == 1) {
      def->addInstance("passthrough","coreir.passthrough",{{"type",c->argType(c->BitIn()->Arr(width))}});
    }
    else if (N == 2) {
      def->addInstance("join",op2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      def->connect("self.in.0","join.in0");
      def->connect("self.in.1","join.in1");
    }
    else {
      def->addInstance("join",op2,{{"width",aWidth}});
      def->connect("join.out","self.out");

      //Connect half instances
      uint Nbits = num_bits(N-1); // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits-1);
      uint Nsmallhalf = N - Nlargehalf;

      cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking into " << Nlargehalf << " and " << Nsmallhalf <<endl;
      Arg* aNlarge = c->argInt(Nlargehalf);
      Arg* aNsmall = c->argInt(Nsmallhalf);

      def->addInstance("opN_0",opN,{{"width",aWidth},{"N",aNlarge},{"operator",aOperator}});
      def->addInstance("opN_1",opN,{{"width",aWidth},{"N",aNsmall},{"operator",aOperator}});
      for (uint i=0; i<Nlargehalf; ++i) {
        def->connect({"self","in",to_string(i)},{"opN_0","in",to_string(i)});
      }
      for (uint i=0; i<Nsmallhalf; ++i) {
        def->connect({"self","in",to_string(i+Nlargehalf)},{"opN_1","in",to_string(i)});
      }
      def->connect("opN_0.out","join.in0");
      def->connect("opN_1.out","join.in1");
    }

  });



  //Add a LUTN
  Params lutNParams({{"N",AINT}});
  commonlib->newTypeGen("lutNType",lutNParams,[](Context* c, Args args) { 
    uint N = args.at("N")->get<ArgInt>();
    ASSERT(N<=5,"NYI due to init bit length");
    return c->Record({
      {"in",c->BitIn()->Arr(N)},
      {"out",c->Bit()}
    });
  });
  Generator* lutN = commonlib->newGeneratorDecl("lutN",commonlib->getTypeGen("lutNType"),lutNParams,{{"init",AINT}});
  lutN->addDefaultConfigArgs({{"init",c->argInt(0)}});
  

  Params MemGenParams = {{"width",AINT},{"depth",AINT}};
  //Linebuffer Memory. Use this for memory in linebuffer mode
  commonlib->newTypeGen("LinebufferMemType",MemGenParams,[](Context* c, Args args) {
    uint width = args.at("width")->get<ArgInt>();
    return c->Record({
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"valid", c->Bit()},
    });
  });
  Generator* lbMem = commonlib->newGeneratorDecl("LinebufferMem",commonlib->getTypeGen("LinebufferMemType"),MemGenParams);
  lbMem->addDefaultGenArgs({{"width",c->argInt(16)},{"depth",c->argInt(1024)}});
  
  //Fifo Memory. Use this for memory in Fifo mode
  commonlib->newTypeGen("FifoMemType",MemGenParams,[](Context* c, Args args) {
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
  Generator* fifoMem = commonlib->newGeneratorDecl("FifoMem",commonlib->getTypeGen("FifoMemType"),MemGenParams,{{"almost_full_cnt",AINT}});
  fifoMem->addDefaultGenArgs({{"width",c->argInt(16)},{"depth",c->argInt(1024)}});

  //TODO RAM

  //Linebuffer
  //Declare a TypeGenerator (in global) for linebuffer
  commonlib->newTypeGen(
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

  Generator* linebuffer = commonlib->newGeneratorDecl(
    "Linebuffer",
    commonlib->getTypeGen("linebuffer_type"),{
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
      def->addInstance(mem_name,"commonlib.LinebufferMem",{{"width",aBitwidth},{"depth",aImageWidth}});
      
      //Add const 1 and term for wen, valid
      string constname = "const1"+c->getUnique();
      string termname = "term"+c->getUnique();
      def->addInstance(constname,"coreir.bitconst",{{"value",c->argInt(1)}});
      def->addInstance(termname,"coreir.bitterm");
      def->connect({constname,"out"},{mem_name,"wen"});
      def->connect({mem_name,"valid"},{termname,"in"});

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








  return commonlib;
}


COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(commonlib)
