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
  
  Params widthparams = Params({{"width",c->Int()}});
  // TypeGens defined in coreirprims

  //muxN type
  commonlib->newTypeGen(
    "muxN_type", //name for the typegen
    {{"width",c->Int()},{"N",c->Int()}}, //generater parameters
    [](Context* c, Values genargs) { //Function to compute type
      uint width = genargs.at("width")->get<int>();
      uint N = genargs.at("N")->get<int>();
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
    {{"width",c->Int()},{"N",c->Int()},{"operator",c->String()}}, //generater parameters
    [](Context* c, Values genargs) { //Function to compute type
      uint width = genargs.at("width")->get<int>();
      uint N = genargs.at("N")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(N)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );


  /////////////////////////////////
  // Commonlib Arithmetic primitives
  //   umin,smin,umax,smax
  //   absd
  /////////////////////////////////

  //Lazy way:
  unordered_map<string,vector<string>> opmap({
    {"binary",{
      "umin","smin","umax","smax","absd"
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
  Generator* notEqual = commonlib->newGeneratorDecl("neq",coreirprims->getTypeGen("binaryReduce"),{{"width",c->Int()}});

  notEqual->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    int width = genargs.at("width")->get<int>();

    Namespace* coreirprims = c->getNamespace("coreir");
    Generator* equal = coreirprims->getGenerator("eq");
    Module* logicalNot = coreirprims->getModule("bitnot");
    
    // create necessary hardware
    Const* aWidth = Const::make(c,width);
    def->addInstance("equal",equal,{{"width",aWidth}});
    def->addInstance("not",logicalNot);

    // connect hardware
    def->connect("self.in0","equal.in0");
    def->connect("self.in1","equal.in1");
    def->connect("equal.out","not.in");
    def->connect("not.out","self.out");

  });

  /////////////////////////////////
  // muxN definition             //
  /////////////////////////////////

  Generator* muxN = commonlib->newGeneratorDecl("muxn",commonlib->getTypeGen("muxN_type"),{{"width",c->Int()},{"N",c->Int()}});
  
  muxN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint N = genargs.at("N")->get<int>();
    assert(N>0);
      Namespace* stdlib = c->getNamespace("coreir");
      Namespace* commonlib = c->getNamespace("commonlib");
      Generator* mux2 = stdlib->getGenerator("mux");
      Generator* passthrough = stdlib->getGenerator("passthrough");
      Generator* muxN = commonlib->getGenerator("muxn");
    
      Const* aWidth = Const::make(c,width);
    
      if (N == 1) {
        def->addInstance("passthrough",passthrough,{{"type",Const::make(c,c->BitIn()->Arr(width))}});
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
        Const* aNlarge = Const::make(c,Nlargehalf);
        Const* aNsmall = Const::make(c,Nsmallhalf);

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

  Generator* opN = commonlib->newGeneratorDecl("opn",commonlib->getTypeGen("opN_type"),{{"width",c->Int()},{"N",c->Int()},{"operator",c->String()}});
  
  opN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint N = genargs.at("N")->get<int>();
    std::string op2 = genargs.at("operator")->get<string>();
    assert(N>0);

    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* opN = commonlib->getGenerator("opn");
    
    Const* aWidth = Const::make(c,width);
    Const* aOperator = Const::make(c,op2);
    
    if (N == 1) {
      def->addInstance("passthrough","coreir.passthrough",{{"type",Const::make(c,c->BitIn()->Arr(width))}});
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
      Const* aNlarge = Const::make(c,Nlargehalf);
      Const* aNsmall = Const::make(c,Nsmallhalf);

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
  auto LUTModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params p; //params
    Values d; //defaults
    int N = genargs.at("N")->get<int>();
    p["N"] = c->BitVector(1<<N);
    return {p,d};
  };

  Params lutNParams({{"N",c->Int()}});
  commonlib->newTypeGen("lutNType",lutNParams,[](Context* c, Values genargs) { 
    uint N = genargs.at("N")->get<int>();
    return c->Record({
      {"in",c->BitIn()->Arr(N)},
      {"out",c->Bit()}
    });
  });
  Generator* lutN = commonlib->newGeneratorDecl("lutN",commonlib->getTypeGen("lutNType"),lutNParams);
  lutN->setModParamsGen(LUTModParamFun);

  Params MemGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  //Linebuffer Memory. Use this for memory in linebuffer mode
  commonlib->newTypeGen("LinebufferMemType",MemGenParams,[](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"valid", c->Bit()},
    });
  });
  Generator* lbMem = commonlib->newGeneratorDecl("LinebufferMem",commonlib->getTypeGen("LinebufferMemType"),MemGenParams);
  lbMem->addDefaultGenArgs({{"width",Const::make(c,16)},{"depth",Const::make(c,1024)}});

  //Fifo Memory. Use this for memory in Fifo mode
  commonlib->newTypeGen("FifoMemType",MemGenParams,[](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"ren", c->BitIn()},
      {"almost_full", c->Bit()},
      {"valid", c->Bit()}
    });
  });
  Generator* fifoMem = commonlib->newGeneratorDecl("FifoMem",commonlib->getTypeGen("FifoMemType"),MemGenParams);
  fifoMem->addDefaultGenArgs({{"width",Const::make(c,16)},{"depth",Const::make(c,1024)}});
  fifoMem->setModParamsGen({{"almost_full_cnt",c->Int()}});

  commonlib->newTypeGen("RamType",MemGenParams,[](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    uint depth = genargs.at("depth")->get<int>();
    uint awidth = (uint) ceil(log2(depth));
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"waddr", c->BitIn()->Arr(awidth)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"raddr", c->BitIn()->Arr(awidth)},
      {"ren", c->BitIn()},
    });
  });
  Generator* ram = commonlib->newGeneratorDecl("Ram",commonlib->getTypeGen("RamType"),MemGenParams);
  ram->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    def->addInstance("mem","coreir.mem",genargs);
    def->addInstance("readreg","coreir.reg",{{"width",genargs["width"]},{"has_en",Const::make(c,true)}});
    def->connect("self.clk","readreg.clk");
    def->connect("self.clk","mem.clk");
    def->connect("self.wdata","mem.wdata");
    def->connect("self.waddr","mem.waddr");
    def->connect("self.wen","mem.wen");
    def->connect("mem.rdata","readreg.in");
    def->connect("self.rdata","readreg.out");
    def->connect("self.raddr","mem.raddr");
    def->connect("self.ren","readreg.en");
  });

  ////TODO add bitvector initialization
  //commonlib->newTypeGen("RomType",MemGenParams,[](Context* c, Values genargs) {
  //  uint width = genargs.at("width")->get<int>();
  //  uint depth = genargs.at("depth")->get<int>();
  //  uint awidth = (uint) ceil(log2(depth));
  //  return c->Record({
  //    {"clk", c->Named("coreir.clkIn")},
  //    {"rdata", c->Bit()->Arr(width)},
  //    {"raddr", c->BitIn()->Arr(awidth)},
  //    {"ren", c->BitIn()},
  //  });
  //});
  //Generator* rom = commonlib->newGeneratorDecl("Rom",commonlib->getTypeGen("RomType"),MemGenParams);
  //rom->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Values genargs) {
  //  def->addInstance("mem","coreir.mem",genargs,TODO Init);
  //  def->wire("self.clk","mem.clk");
  //  def->wire("self.wdata","mem.wdata");
  //  def->wire("self.waddr","mem.waddr");
  //  def->wire("self.wen","mem.wen");
  //  def->wire("mem.rdata","readreg.in");
  //  def->wire("self.rdata","readreg.out");
  //  def->wire("self.raddr","mem.raddr");
  //  def->wire("self.ren","readreg.en");
  //}

  //Linebuffer
  //Declare a TypeGenerator (in global) for linebuffer
  commonlib->newTypeGen(
    "linebuffer_type", //name for the typegen
    {{"stencil_width",c->Int()},{"stencil_height",c->Int()},{"image_width",c->Int()},{"bitwidth",c->Int()}}, //generater parameters
    [](Context* c, Values genargs) { //Function to compute type
      uint stencil_width  = genargs.at("stencil_width")->get<int>();
      uint stencil_height  = genargs.at("stencil_height")->get<int>();
      //uint image_width = genargs.at("image_width")->get<int>();
      uint bitwidth = genargs.at("bitwidth")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(bitwidth)},
        {"wen",c->BitIn()},
          //FIXME: add valid bit
        {"out",c->Bit()->Arr(bitwidth)->Arr(stencil_width)->Arr(stencil_height)}
      });
    }
  );

  Generator* linebuffer = commonlib->newGeneratorDecl(
    "Linebuffer",
    commonlib->getTypeGen("linebuffer_type"),{
      {"stencil_width",c->Int()},
      {"stencil_height",c->Int()},
      {"image_width",c->Int()},
      {"bitwidth",c->Int()}
    }
  );
  linebuffer->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint stencil_width  = genargs.at("stencil_width")->get<int>();
    uint stencil_height  = genargs.at("stencil_height")->get<int>();
    uint image_width = genargs.at("image_width")->get<int>();
    uint bitwidth = genargs.at("bitwidth")->get<int>();
    assert((bitwidth & (bitwidth-1)) == 0); //Check if power of 2
    assert(stencil_height > 0);
    assert(stencil_width > 0);
    assert(image_width >= stencil_width);
    assert(bitwidth > 0);

    if (image_width - stencil_width < 3 && (image_width != stencil_width)) {
      std::cout << "Image width is " << image_width << " and stencil width " << stencil_width
                << ", which means the linebuffer is going to be very small" << std::endl;
    }

    Const* aBitwidth = Const::make(c,bitwidth);
    assert(isa<ConstInt>(aBitwidth));
    Const* aImageWidth = Const::make(c,image_width);
    Namespace* coreirprims = c->getNamespace("coreir");
    std::string reg_prefix = "reg_";
    std::string mem_prefix = "mem_";

    // create the inital register chain
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

    // SPECIAL CASE: same sized stencil as image width, so no memories needed (just registers)
    if (stencil_width == image_width) {
      // connect together the remaining stencil registers
      for (uint i = 1; i < stencil_height; ++i) {
        for (uint j = 1; j < stencil_width; ++j) {
          std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
          def->addInstance(reg_name, "coreir.reg", {{"width",aBitwidth}});
  
          // connect the input
          if (j == 1) {
            std::string prev_reg = reg_prefix + std::to_string(i-1) + "_" + std::to_string(stencil_width-1);
            def->connect({prev_reg, "out"}, {reg_name, "in"});
          } else {
            std::string prev_reg = reg_prefix + std::to_string(i) + "_" + std::to_string(j-1);
            def->connect({prev_reg, "out"}, {reg_name, "in"});
          }
        }
      }

    // REGULAR CASE: memories to store image lines
    } else {
      // connect together the memory lines
      std::string mem_prefix = "mem_";
      for (uint i = 1; i < stencil_height; ++i) {
        std::string mem_name = mem_prefix + std::to_string(i);
        def->addInstance(mem_name,"commonlib.LinebufferMem",{{"width",aBitwidth},{"depth",aImageWidth}});
        def->addInstance(mem_name+"_valid_term", coreirprims->getModule("bitterm"));
        def->connect({mem_name,"valid"},{mem_name+"_valid_term", "in"});
        //def->addInstance(mem_name+"_wen", coreirprims->getModule("bitconst"), {{"value",Const::make(c,1)}});
        def->connect({mem_name,"wen"},{"self", "wen"});

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
    }

    // ALL CASES
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
            if (stencil_width == image_width) { // SPECIAL CASE
              std::string reg_name = reg_prefix + std::to_string(i-1) + "_" + std::to_string(stencil_width-1);
              def->connect({reg_name, "out"}, {"self","out",std::to_string(iflip),std::to_string(jflip)});
            } else { // REGULAR CASE
              std::string mem_name = mem_prefix + std::to_string(i);
              def->connect({mem_name, "rdata"}, {"self","out",std::to_string(iflip),std::to_string(jflip)});
            }
          }
        } else {
          // rest come from registers
          std::string reg_name = reg_prefix + std::to_string(i) + "_" + std::to_string(j);
          def->connect({reg_name, "out"}, {"self","out",std::to_string(iflip),std::to_string(jflip)});
        }
      }
    }    

  });

  
  //////////////////
  //3D Linebuffer //
  //////////////////

  //Declare a TypeGenerator (in global) for 3d linebuffer
  commonlib->newTypeGen(
    "linebuffer_3d_type", //name for the typegen
    {{"stencil_d0",c->Int()},{"stencil_d1",c->Int()},{"stencil_d2",c->Int()},{"image_d0",c->Int()},{"image_d1",c->Int()},{"bitwidth",c->Int()}},
    [](Context* c, Values args) { //Function to compute type
      uint stencil_d0 = args.at("stencil_d0")->get<int>();
      uint stencil_d1 = args.at("stencil_d1")->get<int>();
      uint stencil_d2 = args.at("stencil_d2")->get<int>();
      uint bitwidth = args.at("bitwidth")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(bitwidth)},
        {"wen",c->BitIn()},
          //FIXME: add valid bit
        {"out",c->Bit()->Arr(bitwidth)->Arr(stencil_d0)->Arr(stencil_d1)->Arr(stencil_d2)}
      });
    }
  );

  Generator* linebuffer_3d = commonlib->newGeneratorDecl(
    "Linebuffer_3d",
    commonlib->getTypeGen("linebuffer_3d_type"),{
      {"stencil_d0",c->Int()},
      {"stencil_d1",c->Int()},
      {"stencil_d2",c->Int()},
      {"image_d0",c->Int()},
      {"image_d1",c->Int()},
      {"bitwidth",c->Int()}
    }
  );
  linebuffer_3d->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint stencil_d0  = args.at("stencil_d0")->get<int>();
    uint stencil_d1  = args.at("stencil_d1")->get<int>();
    uint stencil_d2  = args.at("stencil_d2")->get<int>();
    uint image_d0 = args.at("image_d0")->get<int>();
    uint image_d1 = args.at("image_d1")->get<int>();
    uint bitwidth = args.at("bitwidth")->get<int>();
    assert((bitwidth & (bitwidth-1)) == 0); //Check if power of 2
    assert(stencil_d0 > 0);
    assert(stencil_d1 > 0);
    assert(stencil_d2 > 0);
    assert(image_d0 >= stencil_d0);
    assert(image_d1 >= stencil_d1);
    assert(bitwidth > 0);

    Const* aBitwidth = Const::make(c,bitwidth);
    Namespace* coreirprims = c->getNamespace("coreir");

    // create the stencil linebuffers
    std::string lb2_prefix = "lb2_";
    for (uint i=0; i<stencil_d2; ++i) {

      std::string lb2_name = lb2_prefix + std::to_string(i);
      Values args = {
        {"stencil_width",Const::make(c,stencil_d0)},
        {"stencil_height",Const::make(c,stencil_d1)},
        {"image_width",Const::make(c,image_d0)},
        {"bitwidth",aBitwidth}
      };
      def->addInstance(lb2_name, "commonlib.Linebuffer", args);
      def->connect({lb2_name, "wen"}, {"self","wen"});
    }      

    // SPECIAL CASE: same sized stencil as image, so no memories needed (just lbs)
    if (stencil_d1 == image_d1) {
      // connect the linebuffer inputs
      for (uint i = 0; i < stencil_d2; ++i) {
        std::string lb_name = lb2_prefix + std::to_string(i);

        if (i == 0) {
          def->connect({"self","in"},{lb_name,"in"});
        } else {
          std::string prev_lb = lb2_prefix + std::to_string(i-1);
          def->connect({prev_lb,"0","0"},{lb_name,"in"});
        }
      }

    // REGULAR CASE: memories to store image lines
    } else {
      // connect together the memory lines
      std::string mem_prefix = "mem_";
      for (uint i = 1; i < stencil_d2; ++i) {
        std::string mem_name = mem_prefix + std::to_string(i);
        Const* aLBWidth = Const::make(c,image_d1 * image_d0);
        def->addInstance(mem_name,"commonlib.LinebufferMem",{{"width",aBitwidth},{"depth",aLBWidth}});
        def->addInstance(mem_name+"_valid_term", coreirprims->getModule("bitterm"));
        def->connect({mem_name,"valid"},{mem_name+"_valid_term", "in"});
        def->connect({mem_name,"wen"},{"self", "wen"});

        // connect the input
        if (i == 1) {
          def->connect({"self","in"}, {mem_name, "wdata"});
        } else {
          std::string prev_mem = mem_prefix + std::to_string(i-1);
          def->connect({prev_mem, "rdata"}, {mem_name, "wdata"});
        }
      }

      // connect memory outs to stencil linebuffers
      for (uint i = 1; i < stencil_d2; ++i) {
        std::string mem_name = mem_prefix + std::to_string(i);
        std::string lb_name = lb2_prefix + std::to_string(i);
        def->connect({mem_name, "rdata"},{lb_name, "in"});
      }
    }

    // ALL CASES: connect the stencil outputs
    for (uint i = 0; i < stencil_d2; ++i) {
      uint iflip = (stencil_d2 - 1) - i;
      std::string lb_name = lb2_prefix + std::to_string(i);
      def->connect({"self","out",std::to_string(iflip)}, {lb_name,"out"});
    }

  });


  /////////////////////////////////
  // counter definition          //
  /////////////////////////////////

  // counter follows a for loop of format:
  //   for ( int i = $min ; $min < $max ; i += $inc )
  // input:  "valid", when to start counting
  // output: "i", the count

  // counter type
  commonlib->newTypeGen(
    "counter_type", //name for the typegen
    {{"width",c->Int()},{"min",c->Int()},{"max",c->Int()},{"inc",c->Int()}}, //generater parameters
    [](Context* c, Values genargs) { //Function to compute type
      uint width = genargs.at("width")->get<int>();
      return c->Record({
        {"en",c->BitIn()},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

  Generator* counter = commonlib->newGeneratorDecl("counter",commonlib->getTypeGen("counter_type"),{{"width",c->Int()},{"min",c->Int()},{"max",c->Int()},{"inc",c->Int()}});
  
  counter->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint max = genargs.at("max")->get<int>();
    uint min = genargs.at("min")->get<int>();
    uint inc = genargs.at("inc")->get<int>();
    assert(width>0);
    assert(max>min);

    // get generators
    Namespace* coreirprims = c->getNamespace("coreir");
    Module* and_mod = coreirprims->getModule("bitand");
    Generator* ult_gen = coreirprims->getGenerator("ult");
    Generator* add_gen = coreirprims->getGenerator("add");
    Generator* reg_gen = coreirprims->getGenerator("reg");
    Generator* const_gen = coreirprims->getGenerator("const");
    
    // create hardware
    Const* aBitwidth = Const::make(c,width);
    Const* aReset = Const::make(c,BitVector(width,min));
    def->addInstance("count", reg_gen, {{"width",aBitwidth},{"clr",Const::make(c,true)},{"en",Const::make(c,true)}},
                         {{"init",aReset}});

    def->addInstance("max", const_gen, {{"width",aBitwidth}}, {{"value",Const::make(c,BitVector(width,max))}});
    def->addInstance("inc", const_gen, {{"width",aBitwidth}}, {{"value",Const::make(c,BitVector(width,inc))}});
    def->addInstance("ult", ult_gen, {{"width",aBitwidth}});
    def->addInstance("add", add_gen, {{"width",aBitwidth}});
    def->addInstance("and", and_mod);
    
    // wire up modules
    // clear if count+inc > max
    def->connect("count.out","self.out");
    def->connect("count.out","add.in0");
    def->connect("inc.out","add.in1");

    def->connect("self.en","count.en");
    def->connect("add.out","count.in");

    def->connect("add.out","ult.in1");
    def->connect("max.out","ult.in0");
    def->connect("ult.out","count.clr");

  });

  /////////////////////////////////
  // serializer definition       //
  /////////////////////////////////

  // on count==0, read in all input values.
  // on every cycle, input<n> is outputted where n=count

  // serializer type
  commonlib->newTypeGen(
    "serializer_type", //name for the typegen
    {{"width",c->Int()},{"rate",c->Int()}}, //generater parameters
    [](Context* c, Values args) { //Function to compute type
      uint width = args.at("width")->get<int>();
      uint rate  = args.at("rate")->get<int>();
      return c->Record({
        {"en",c->BitIn()},
        {"count",c->Bit()->Arr(width)},
        {"in",c->BitIn()->Arr(width)->Arr(rate)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

  Generator* serializer = commonlib->newGeneratorDecl("serializer",commonlib->getTypeGen("serializer_type"),{{"width",c->Int()},{"rate",c->Int()}});
  
  serializer->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    uint rate  = args.at("rate")->get<int>();
    assert(width>0);
    assert(rate>1);

    // get generators
    Namespace* coreirprims = c->getNamespace("coreir");
    Generator* const_gen = coreirprims->getGenerator("const");
    Generator* eq_gen = coreirprims->getGenerator("eq");
    
    // create hardware
    Const* aBitwidth = Const::make(c,width);
    def->addInstance("counter", "commonlib.counter",
                     {{"width",aBitwidth},{"min",Const::make(c,0)},{"max",Const::make(c,rate)},{"inc",Const::make(c,1)}});
    def->addInstance("muxn", "commonlib.muxn",
                     {{"width",aBitwidth},{"N",Const::make(c,rate)}});
    def->addInstance("equal", eq_gen,
                     {{"width",aBitwidth}});
    def->addInstance("zero", const_gen,
                     {{"width",aBitwidth}},{{"value",Const::make(c,BitVector(width,0))}});

    // all but input0 are stored in registers
    for (uint i=1; i<rate; ++i) {
      std::string reg_name = "reg_" + std::to_string(i);
      def->addInstance(reg_name, "coreir.reg",
                       {{"width",aBitwidth},{"en",Const::make(c,true)}});
    }

    // wire up modules
    def->connect("self.en","counter.en");
    def->connect("counter.out","self.count");
    def->connect("counter.out","muxn.in.sel");

    def->connect("zero.out","equal.in0");
    def->connect("counter.out","equal.in1");
    

    // wire up inputs to regs and mux
    for (uint i=0; i<rate; ++i) {
      std::string idx = std::to_string(i);
      if (i==0) {
        def->connect("self.in.0", "muxn.in.data.0");
      } else {
        std::string reg_name = "reg_"+idx;
        def->connect("self.in."+idx, reg_name+".in");
        def->connect(reg_name+".out", "muxn.in.data."+idx);

        // connect reg enables
        def->connect(reg_name+".en", "equal.out");
      }
    }
    
    def->connect("muxn.out","self.out");

  });


  /////////////////////////////////
  // decoder definition          //
  /////////////////////////////////

  // on count==0, read in all input values.
  // on every cycle, input<n> is outputted where n=count

  // Not yet implemented

  return commonlib;
}


COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(commonlib)
