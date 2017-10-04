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
    [](Context* c, Values args) { //Function to compute type
      uint width = args.at("width")->get<int>();
      uint N = args.at("N")->get<int>();
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
    {{"width",c->Int()},{"N",c->Int()},{"operator",ASTRING}}, //generater parameters
    [](Context* c, Values args) { //Function to compute type
      uint width = args.at("width")->get<int>();
      uint N = args.at("N")->get<int>();
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
  Generator* notEqual = commonlib->newGeneratorDecl("neq",coreirprims->getTypeGen("binaryReduce"),{{"width",c->Int()}});

  notEqual->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Values genargs) {
    uint width = args.at("width")->get<int>();

    Namespace* coreirprims = c->getNamespace("coreir");
    Generator* equal = coreirprims->getGenerator("eq");
    Module* logicalNot = coreirprims->getModule("bitnot");
    
    // create necessary hardware
    ArgPtr aWidth = Const::make(c,width);
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
  
  muxN->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Values args) {
    uint width = args.at("width")->get<int>();
    uint N = args.at("N")->get<int>();
    assert(N>0);
      Namespace* stdlib = c->getNamespace("coreir");
      Namespace* commonlib = c->getNamespace("commonlib");
      Generator* mux2 = stdlib->getGenerator("mux");
      Generator* passthrough = stdlib->getGenerator("passthrough");
      Generator* muxN = commonlib->getGenerator("muxn");
    
      ArgPtr aWidth = Const::make(c,width);
    
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
        ArgPtr aNlarge = Const::make(c,Nlargehalf);
        ArgPtr aNsmall = Const::make(c,Nsmallhalf);

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

  Generator* opN = commonlib->newGeneratorDecl("opn",commonlib->getTypeGen("opN_type"),{{"width",c->Int()},{"N",c->Int()},{"operator",ASTRING}});
  
  opN->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Values args) {
    uint width = args.at("width")->get<int>();
    uint N = args.at("N")->get<int>();
    std::string op2 = args.at("operator")->get<string>();
    assert(N>0);

    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* opN = commonlib->getGenerator("opn");
    
    ArgPtr aWidth = Const::make(c,width);
    ArgPtr aOperator = Const::make(c,op2);
    
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
      ArgPtr aNlarge = Const::make(c,Nlargehalf);
      ArgPtr aNsmall = Const::make(c,Nsmallhalf);

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
  Params lutNParams({{"N",c->Int()}});
  commonlib->newTypeGen("lutNType",lutNParams,[](Context* c, Values args) { 
    uint N = args.at("N")->get<int>();
    ASSERT(N<=5,"NYI due to init bit length");
    return c->Record({
      {"in",c->BitIn()->Arr(N)},
      {"out",c->Bit()}
    });
  });
  Generator* lutN = commonlib->newGeneratorDecl("lutN",commonlib->getTypeGen("lutNType"),lutNParams,{{"init",c->Int()}});
  lutN->addDefaultConfigArgs({{"init",Const::make(c,0)}});
  

  Params MemGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  //Linebuffer Memory. Use this for memory in linebuffer mode
  commonlib->newTypeGen("LinebufferMemType",MemGenParams,[](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
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
  commonlib->newTypeGen("FifoMemType",MemGenParams,[](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
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
  Generator* fifoMem = commonlib->newGeneratorDecl("FifoMem",commonlib->getTypeGen("FifoMemType"),MemGenParams,{{"almost_full_cnt",c->Int()}});
  fifoMem->addDefaultGenArgs({{"width",Const::make(c,16)},{"depth",Const::make(c,1024)}});

  commonlib->newTypeGen("RamType",MemGenParams,[](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
    uint depth = args.at("depth")->get<int>();
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
  ram->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Values genargs) {
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
  //commonlib->newTypeGen("RomType",MemGenParams,[](Context* c, Values args) {
  //  uint width = args.at("width")->get<int>();
  //  uint depth = args.at("depth")->get<int>();
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
    [](Context* c, Values args) { //Function to compute type
      uint stencil_width  = args.at("stencil_width")->get<int>();
      uint stencil_height  = args.at("stencil_height")->get<int>();
      //uint image_width = args.at("image_width")->get<int>();
      uint bitwidth = args.at("bitwidth")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(bitwidth)},
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
  linebuffer->setGeneratorDefFromFun([](ModuleDef* def,Context* c, Type* t, Values args) {
    uint stencil_width  = args.at("stencil_width")->get<int>();
    uint stencil_height  = args.at("stencil_height")->get<int>();
    uint image_width = args.at("image_width")->get<int>();
    uint bitwidth = args.at("bitwidth")->get<int>();
    assert((bitwidth & (bitwidth-1)) == 0); //Check if power of 2
    assert(stencil_height > 0);
    assert(stencil_width > 0);
    assert(image_width > stencil_width);
    assert(bitwidth > 0);

    ArgPtr aBitwidth = Const::make(c,bitwidth);
    assert(isa<ArgInt>(aBitwidth));
    ArgPtr aImageWidth = Const::make(c,image_width);
    Namespace* coreirprims = c->getNamespace("coreir");

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
      def->addInstance(mem_name+"_valid_term", coreirprims->getModule("bitterm"));
      def->connect({mem_name,"valid"},{mem_name+"_valid_term", "in"});
      def->addInstance(mem_name+"_wen", coreirprims->getModule("bitconst"), {{"value",Const::make(c,1)}});
      def->connect({mem_name,"wen"},{mem_name+"_wen", "out"});

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
    [](Context* c, Values args) { //Function to compute type
      uint width = args.at("width")->get<int>();
      return c->Record({
        {"en",c->BitIn()},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );

  Generator* counter = commonlib->newGeneratorDecl("counter",commonlib->getTypeGen("counter_type"),{{"width",c->Int()},{"min",c->Int()},{"max",c->Int()},{"inc",c->Int()}});
  
  counter->setGeneratorDefFromFun([](ModuleDef* def, Context* c, Type* t, Values args) {
    uint width = args.at("width")->get<int>();
    uint max = args.at("max")->get<int>();
    uint min = args.at("min")->get<int>();
    uint inc = args.at("inc")->get<int>();
    assert(width>0);
    assert(max>min);

    // get generators
    Namespace* coreirprims = c->getNamespace("coreir");
    Module* and_mod = coreirprims->getModule("bitand");
    //Generator* mux_gen = coreirprims->getGenerator("mux");
    Generator* ult_gen = coreirprims->getGenerator("ult");
    Generator* add_gen = coreirprims->getGenerator("add");
    Generator* reg_gen = coreirprims->getGenerator("reg");
    Generator* const_gen = coreirprims->getGenerator("const");
    
    // create hardware
    ArgPtr aBitwidth = Const::make(c,width);
    ArgPtr aReset = Const::make(c,min);
    def->addInstance("count", reg_gen, {{"width",aBitwidth},{"clr",Const::make(c,true)},{"en",Const::make(c,true)}},
                     {{"init",aReset}});

    //def->addInstance("min", const_gen, {{"width",aBitwidth}}, {{"value",Const::make(c,min)}});
    def->addInstance("max", const_gen, {{"width",aBitwidth}}, {{"value",Const::make(c,max)}});
    def->addInstance("inc", const_gen, {{"width",aBitwidth}}, {{"value",Const::make(c,inc)}});
    def->addInstance("ult", ult_gen, {{"width",aBitwidth}});
    def->addInstance("add", add_gen, {{"width",aBitwidth}});
    def->addInstance("and", and_mod);
    //    def->addInstance("mux", mux_gen, {{"width",aBitwidth}});
    
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
    //    def->connect("ult.out","and.in.0");
    //    def->connect("self.en","and.in.1");

    //    def->connect("add.out","mux.in.data.1");
    //    def->connect("min.out","mux.in.data.0");
    //    def->connect("mux.out","count.in");

  });


  return commonlib;
}


COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(commonlib)
