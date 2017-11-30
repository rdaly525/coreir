//This file is just included in context.cpp

bool isPowerOfTwo(const uint n) {
  if (n == 0) {
    return 0;
  }

  return (n & (n - 1)) == 0;
}

Namespace* CoreIRLoadHeader_memory(Context* c) {
  
  Namespace* memory = c->newNamespace("memory");
  



  Params RomGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  auto RomModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    int width = genargs.at("width")->get<int>();
    int depth = genargs.at("depth")->get<int>();
    modparams["init"] = BitVectorType::make(c,width*);
    defaultargs["init"] = Const::make(c,BitVector(width,0));
    return {modparams,defaultargs};
  };
  
  commonlib->newTypeGen("LinebufferMemType",MemGenParams,[](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
	// Is this just wen delayed by N?
      {"valid", c->Bit()},
    });
  });




  Params MemGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  //Linebuffer Memory. Use this for memory in linebuffer mode
  commonlib->newTypeGen("LinebufferMemType",MemGenParams,[](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
	// Is this just wen delayed by N?
      {"valid", c->Bit()},
    });
  });
  Generator* lbMem = commonlib->newGeneratorDecl("LinebufferMem",commonlib->getTypeGen("LinebufferMemType"),MemGenParams);
  lbMem->addDefaultGenArgs({{"width",Const::make(c,16)},{"depth",Const::make(c,1024)}});

  lbMem->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    //uint width = genargs.at("width")->get<int>();
    uint depth = genargs.at("depth")->get<int>();
    uint awidth = (uint) ceil(log2(depth));

    def->addInstance("raddr","mantle.reg",{{"width",Const::make(c,awidth)},{"has_en",Const::make(c,true)}});
    def->addInstance("waddr","mantle.reg",{{"width",Const::make(c,awidth)},{"has_en",Const::make(c,true)}});

    def->addInstance("mem","coreir.mem",genargs);

    def->addInstance("add_r","coreir.add",{{"width",Const::make(c,awidth)}});
    def->addInstance("add_w","coreir.add",{{"width",Const::make(c,awidth)}});
    def->addInstance("c1","coreir.const",{{"width",Const::make(c,awidth)}},{{"value",Const::make(c,awidth,1)}});

    if (!isPowerOfTwo(depth)) {

      // Multiplexers to check max value
      def->addInstance("raddr_mux", "coreir.mux", {{"width", Const::make(c, awidth)}});
      def->addInstance("waddr_mux", "coreir.mux", {{"width", Const::make(c, awidth)}});

      // Equals to test if addresses are at the max
      def->addInstance("raddr_eq", "coreir.eq", {{"width", Const::make(c, awidth)}});
      def->addInstance("waddr_eq", "coreir.eq", {{"width", Const::make(c, awidth)}});
    
      // Reset constant
      def->addInstance("zero_const",
                       "coreir.const",
                       {{"width",Const::make(c,awidth)}},
                       {{"value", Const::make(c, awidth, 0)}});

      // Max constant
      def->addInstance("max_const",
                       "coreir.const",
                       {{"width",Const::make(c,awidth)}},
                       // Fix this for 64 bit constants!
                       {{"value", Const::make(c, awidth, depth)}}); //(1 << awidth) - 1)}});

      // Wire up the resets
      def->connect("raddr_eq.out", "raddr_mux.sel");
      def->connect("waddr_eq.out", "waddr_mux.sel");

      def->connect("zero_const.out", "raddr_mux.in1");
      def->connect("zero_const.out", "waddr_mux.in1");

      def->connect("add_r.out", "raddr_mux.in0");
      def->connect("add_w.out", "waddr_mux.in0");

      def->connect("waddr_mux.out", "waddr.in");
      def->connect("raddr_mux.out", "raddr.in");

      // Wire up equals inputs
      def->connect("add_r.out", "raddr_eq.in0");
      def->connect("max_const.out", "raddr_eq.in1");

      def->connect("add_w.out", "waddr_eq.in0");
      def->connect("max_const.out", "waddr_eq.in1");

    } else {
      def->connect("add_r.out","raddr.in");    
      def->connect("add_w.out","waddr.in");
    }

    // Wire up the rest of the circuit
    def->connect("self.wdata","mem.wdata");

    def->connect("self.wen","mem.wen");
    def->connect("self.clk","mem.clk");

    def->connect("waddr.out","mem.waddr");
    def->connect("raddr.out","mem.raddr");
    def->connect("mem.rdata","self.rdata");


    def->connect("add_r.in0","raddr.out");
    def->connect("add_r.in1","c1.out");

    def->connect("waddr.en","self.wen");
    def->connect("waddr.clk","self.clk");

    def->connect("raddr.en","self.wen");
    def->connect("raddr.clk","self.clk");

    def->connect("add_w.in0","waddr.out");
    def->connect("add_w.in1","c1.out");

    def->addInstance("veq","coreir.neq",{{"width",Const::make(c,awidth)}});
    def->connect("veq.in0","raddr.out");
    def->connect("veq.in1","waddr.out");
    def->connect("veq.out","self.valid");
  });





  return memory;
}


//module #(parameter lbmem {
//  input clk,
//  input [W-1:0] wdata,
//  input wen,
//  output [W-1:0] rdata,
//  output valid
//}
//
//  reg [A-1] raddr
//  reg [A-1] waddr;
//  
//  always @(posedge clk) begin
//    if (wen) waddr <= waddr + 1;
//  end
//  assign valid = waddr!=raddr; 
//  always @(posedge clk) begin
//    if (valid) raddr <= raddr+1;
//  end
//
//  coreir_mem inst(
//    .clk(clk),
//    .wdata(wdata),
//    .waddr(wptr),
//    .wen(wen),
//    .rdata(rdata),
//    .raddr(rptr)
//  );
//
//endmodule

