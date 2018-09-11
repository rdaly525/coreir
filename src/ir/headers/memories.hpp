//This file is just included in context.cpp

bool isPowerOfTwo(const uint n) {
  if (n == 0) {
    return 0;
  }

  return (n & (n - 1)) == 0;
}

Namespace* CoreIRLoadHeader_memory(Context* c) {

  Namespace* memory = c->newNamespace("memory");

  Params MemGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  //Linebuffer Memory. Use this for memory in linebuffer mode
  memory->newTypeGen("rowbufferType",MemGenParams,[](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"rdata", c->Bit()->Arr(width)},
      {"valid", c->Bit()},
      {"flush", c->BitIn()},
    });
  });

  //Note this is a linebuffer MEMORY (a single row) and not a full linebuffer.
  Generator* lbMem = memory->newGeneratorDecl("rowbuffer",memory->getTypeGen("rowbufferType"),MemGenParams);

  lbMem->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint depth = genargs.at("depth")->get<int>();
    uint addrWidth = (uint) ceil(log2(depth));

    Values awParams({{"width",Const::make(c,addrWidth)}});
    Values aw1Params({{"width",Const::make(c,addrWidth+1)}});

    //All State (mem, waddr, raddr, valid)
    def->addInstance("mem","coreir.mem",genargs);

    def->addInstance("raddr","mantle.counter",{{"width",Const::make(c,addrWidth)},{"has_max",Const::make(c,true)},{"has_en",Const::make(c,true)},{"has_srst",Const::make(c,true)}},{{"max",Const::make(c,addrWidth,depth-1)}});
    def->addInstance("waddr","mantle.counter",{{"width",Const::make(c,addrWidth)},{"has_max",Const::make(c,true)},{"has_en",Const::make(c,true)},{"has_srst",Const::make(c,true)}},{{"max",Const::make(c,addrWidth,depth-1)}});
    def->addInstance("cnt","mantle.reg",{{"width",Const::make(c,addrWidth+1)},{"has_en",Const::make(c,true)},{"has_clr",Const::make(c,true)}},{{"init",Const::make(c,BitVector(addrWidth+1,0))}});

    def->addInstance("state","mantle.reg",{{"width",Const::make(c,1)},{"has_en",Const::make(c,true)},{"has_clr",Const::make(c,true)}},{{"init",Const::make(c,1,0)}});


    def->addInstance("out_and_wen","corebit.and");

    //Constants:
    //def->addInstance("c0","coreir.const",aw1Params,{{"value",Const::make(c,addrWidth+1,0)}});
    def->addInstance("c1","corebit.const",{{"value",Const::make(c,true)}});

    //All clk connections:
    def->connect("self.clk","mem.clk");
    def->connect("self.clk","raddr.clk");
    def->connect("self.clk","waddr.clk");
    def->connect("self.clk","cnt.clk");
    def->connect("self.clk","state.clk");

    //mem connections
    def->connect("raddr.out","mem.raddr");
    def->connect("waddr.out","mem.waddr");
    def->connect("mem.rdata","self.rdata");
    def->connect("self.wdata","mem.wdata");
    def->connect("self.wen","mem.wen");

    //Other IO
    def->connect("self.valid","out_and_wen.out");
    def->connect("state.out.0","out_and_wen.in0");
    def->connect("self.wen","out_and_wen.in1");

    //Logic to drive raddr
    def->connect("out_and_wen.out","raddr.en");
    def->connect("self.flush","raddr.srst");

    //Logic to drive waddr
    def->connect("self.wen","waddr.en");
    def->connect("self.flush","waddr.srst");

    //Logic to drive cnt
    // cnt_n = !state ? cnt+wen
    def->addInstance("state0","corebit.not");
    def->addInstance("add_wen","coreir.add",aw1Params);
    def->addInstance("wen_ext","coreir.zext",{{"width_in",Const::make(c,1)},{"width_out",Const::make(c,addrWidth+1)}});
    def->connect("self.flush","cnt.clr");
    def->connect("state.out.0","state0.in");
    def->connect("state0.out","cnt.en");
    def->connect("self.wen","wen_ext.in.0");
    def->connect("wen_ext.out","add_wen.in0");
    def->connect("cnt.out","add_wen.in1");
    def->connect("add_wen.out","cnt.in");

    //Logic to drive state
    //state_n = flush ? 0 :  (cnt_n == DEPTH) ? 1 : state
    //def->addInstance("state_n","corebit.mux");
    def->addInstance("depth_m1","coreir.const",aw1Params,{{"value",Const::make(c,addrWidth+1,depth)}});
    def->addInstance("eq_depth","coreir.eq",aw1Params);
    def->connect("self.flush","state.clr");
    def->connect("depth_m1.out","eq_depth.in0");
    def->connect("add_wen.out","eq_depth.in1");
    def->connect("eq_depth.out","state.en");
    def->connect("c1.out","state.in.0");
  });


  //Fifo Memory. Use this for memory in Fifo mode
  memory->newTypeGen("FifoMemType",MemGenParams,[](Context* c, Values genargs) {
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
  Generator* fifoMem = memory->newGeneratorDecl("fifo",memory->getTypeGen("FifoMemType"),MemGenParams);
  fifoMem->addDefaultGenArgs({{"width",Const::make(c,16)},{"depth",Const::make(c,1024)}});
  fifoMem->setModParamsGen({{"almost_full_cnt",c->Int()}});

  fifoMem->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
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



  memory->newTypeGen("RamType",MemGenParams,[](Context* c, Values genargs) {
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

  //This has a 1 cycle read delay
  //TODO describe the read after write behavior
  //TODO add in parameterized read after write behavior and the read delay
  Generator* ram = memory->newGeneratorDecl("ram",memory->getTypeGen("RamType"),MemGenParams);
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


  Params RomGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  auto RomModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params modparams;
    Values defaultargs;
    modparams["init"] = JsonType::make(c);
    return {modparams,defaultargs};
  };

  memory->newTypeGen("RomType",MemGenParams,[](Context* c, Values genargs) {
    uint width = genargs.at("width")->get<int>();
    uint depth = genargs.at("depth")->get<int>();
    uint awidth = (uint) ceil(log2(depth));
    return c->Record({
      {"clk", c->Named("coreir.clkIn")},
      {"rdata", c->Bit()->Arr(width)},
      {"raddr", c->BitIn()->Arr(awidth)},
      {"ren", c->BitIn()},
    });
  });


  Generator* rom = memory->newGeneratorDecl("rom",memory->getTypeGen("RomType"),MemGenParams);
  rom->setModParamsGen(RomModParamFun);
  rom->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint depth = genargs.at("depth")->get<int>();
    uint awidth = (uint) ceil(log2(depth));

    Values memargs = genargs;
    memargs.insert({"has_init",Const::make(c,true)});

    def->addInstance("mem","coreir.mem",memargs,{{"init",def->getModule()->getArg("init")}});
    def->addInstance("readreg","coreir.reg",{{"width",Const::make(c,width)},{"has_en",Const::make(c,true)}});
    def->addInstance("wdata0","coreir.const",{{"width",Const::make(c,width)}},{{"value",Const::make(c,0)}});
    def->addInstance("waddr0","coreir.const",{{"width",Const::make(c,awidth)}},{{"value",Const::make(c,0)}});
    def->connect("self.clk","mem.clk");
    def->connect("self.clk","readreg.clk");
    def->connect("wdata0","mem.wdata");
    def->connect("waddr0","mem.waddr");
    def->connect("wdata0.0","mem.wen");
    def->connect("mem.rdata","readreg.in");
    def->connect("self.rdata","readreg.out");
    def->connect("self.raddr","mem.raddr");
    def->connect("self.ren","readreg.en");
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

