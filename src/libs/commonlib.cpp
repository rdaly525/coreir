#include "coreir/libs/commonlib.h"
#include "coreir/libs/aetherlinglib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(commonlib);

using namespace std;
using namespace CoreIR;

uint num_bits(uint N) {
  if (N==0) { return 1; }

  uint num_shifts = 0;
  uint temp_value = N;
  while (temp_value > 0) {
    temp_value  = temp_value >> 1;
    num_shifts++;
  }
  return num_shifts;
}

// returns vector starting with bitwidth
// array[bitwidth][dim1][dim2] -> {bitwidth,dim1,dim2
vector<uint> get_dims(Type* type) {
  vector<uint> lengths;
  uint bitwidth = 1;
  Type* cType = type;
  while(!cType->isBaseType()) {
    if (auto aType = dyn_cast<ArrayType>(cType)) {
      
      uint length = aType->getLen();
          
      cType = aType->getElemType();
      if (cType->isBaseType()) {
        bitwidth = length;
      } else {
        lengths.insert(lengths.begin(), length);
        //lengths.push_back(length);
      }
    }
  }

  lengths.insert(lengths.begin(), bitwidth);
  return lengths;
}

// returns number of arraytypes that are nested (not ignoring bitwidth)
uint num_dims(Type* type) {
  uint num_dims = 0;

  Type* cType = type;
  while(!cType->isBaseType()) {
    assert(cType->getKind() == Type::TypeKind::TK_Array);
    ArrayType* aType = static_cast<ArrayType*>(cType);
    cType = aType->getElemType();
    
    num_dims++;
  }
  return num_dims;
}

bool isPowerOfTwo(const uint n) {
  if (n == 0) {
    return 0;
  }

  return (n & (n - 1)) == 0;
}

uint inverted_index(uint outx, uint inx, uint i) {
  return (outx-1) - (inx-1 - i % inx) - (i / inx) * inx;
}

vector<CoreIR::Wireable*> get_wires(CoreIR::Wireable* base_wire, const vector<size_t> ports) {
  int num_ports = 1;
  for (const auto& port_length : ports) {
    num_ports *= port_length;
  }

  vector<CoreIR::Wireable*> all_wires(num_ports);

  vector<uint> port_idxs(ports.size());
    
  for (int idx = 0; idx < num_ports; ++idx) {
    // find the wire associated with the indices
    CoreIR::Wireable* cur_wire = base_wire;
    for (const auto& port_idx : port_idxs) {
      cur_wire = cur_wire->sel(port_idx);
    }

    // add the wire to our list
    all_wires.at(idx) = cur_wire;
    
    // increment  index
    port_idxs.at(0) += 1;
    for (size_t dim = 0; dim < port_idxs.size(); ++dim) {
      if (port_idxs.at(dim) >= ports.at(dim)) {
        port_idxs.at(dim) = 0;
        if (dim + 1 < port_idxs.size()) {
          port_idxs.at(dim+1) += 1;
        }
      }
    }
  }
    
  return all_wires;
}


void connect_wires(ModuleDef *def, vector<Wireable*> in_wires, vector<Wireable*> out_wires) {
  assert(in_wires.size() == out_wires.size());
  
  for (size_t idx=0; idx<in_wires.size(); ++idx) {
    def->connect(in_wires.at(idx), out_wires.at(idx));
  }
}

Namespace* CoreIRLoadLibrary_commonlib(Context* c) {

  Namespace* commonlib = c->newNamespace("commonlib");
  Namespace* coreirprims = c->getNamespace("coreir");

  /////////////////////////////////
  // Commonlib Types
  /////////////////////////////////

  Params widthparams = Params({{"width",c->Int()}});
  // TypeGens defined in coreirprims

  //For MAD
  coreirprims->newTypeGen(
    "ternary",
    widthparams,
    [](Context* c, Values args) {
      uint width = args.at("width")->get<int>();
      Type* ptype = c->Bit()->Arr(width);
      return c->Record({
        {"in0",c->Flip(ptype)},
        {"in1",c->Flip(ptype)},
        {"in2",c->Flip(ptype)},
        {"out",ptype}
      });
    }
  );

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
              {"sel",c->BitIn()->Arr(num_bits(N-1))}
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

  //bitopN type
  commonlib->newTypeGen(
    "bitopN_type", //name for the typegen
    {{"N",c->Int()},{"operator",c->String()}}, //generater parameters
    [](Context* c, Values genargs) { //Function to compute type
      uint N = genargs.at("N")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(N)},
        {"out",c->Bit()}
      });
    }
  );


  /////////////////////////////////
  // Commonlib Arithmetic primitives
  //   umin,smin,umax,smax
	//   uclamp, sclamp
  //   abs, absd, MAD
  //   div
  /////////////////////////////////

  //Lazy way:
  unordered_map<string,vector<string>> opmap({
      {"unary",{
          "abs"
    }},
    {"binary",{
      "umin","smin","umax","smax",
      "uclamp","sclamp",
      "absd", "div",
    }},
    {"ternary",{
        "MAD"
    }},
  });

  //Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = coreirprims->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      commonlib->newGeneratorDecl(op,tg,widthparams);
    }
  }

  //*** Define min/max modules ***//

  Generator* umin = c->getGenerator("commonlib.umin");
  umin->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width==16,"NYI non 16");
    def->addInstance("ucomp","coreir.ule",args);
    def->addInstance("min_mux","coreir.mux",args);
    def->connect("self.in0","ucomp.in0");
    def->connect("self.in1","ucomp.in1");
    def->connect("ucomp.out","min_mux.sel");
    def->connect("self.in1","min_mux.in0");
    def->connect("self.in0","min_mux.in1");
    def->connect("self.out","min_mux.out");
  });

  Generator* smin = c->getGenerator("commonlib.smin");
  smin->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width==16,"NYI non 16");
    def->addInstance("scomp","coreir.sle",args);
    def->addInstance("min_mux","coreir.mux",args);
    def->connect("self.in0","scomp.in0");
    def->connect("self.in1","scomp.in1");
    def->connect("scomp.out","min_mux.sel");
    def->connect("self.in1","min_mux.in0");
    def->connect("self.in0","min_mux.in1");
    def->connect("self.out","min_mux.out");
  });

  Generator* umax = c->getGenerator("commonlib.umax");
  umax->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width==16,"NYI non 16");
    def->addInstance("ucomp","coreir.uge",args);
    def->addInstance("max_mux","coreir.mux",args);
    def->connect("self.in0","ucomp.in0");
    def->connect("self.in1","ucomp.in1");
    def->connect("ucomp.out","max_mux.sel");
    def->connect("self.in1","max_mux.in0");
    def->connect("self.in0","max_mux.in1");
    def->connect("self.out","max_mux.out");
  });

  Generator* smax = c->getGenerator("commonlib.smax");
  smax->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width==16,"NYI non 16");
    def->addInstance("scomp","coreir.sge",args);
    def->addInstance("max_mux","coreir.mux",args);
    def->connect("self.in0","scomp.in0");
    def->connect("self.in1","scomp.in1");
    def->connect("scomp.out","max_mux.sel");
    def->connect("self.in1","max_mux.in0");
    def->connect("self.in0","max_mux.in1");
    def->connect("self.out","max_mux.out");
  });

  //*** Define clamp ***//
  Generator* uclamp = c->getGenerator("commonlib.uclamp");
  uclamp->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("max","coreir.umax",args);
    def->addInstance("min","coreir.umin",args);
    def->connect("self.in0","max.in0");
    def->connect("self.in1","max.in1");
    def->connect("self.in2","min.in0");
    def->connect("max.out","min.in1");
    def->connect("self.out","min.out");
  });

  Generator* sclamp = c->getGenerator("commonlib.sclamp");
  sclamp->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("max","coreir.smax",args);
    def->addInstance("min","coreir.smin",args);
    def->connect("self.in0","max.in0");
    def->connect("self.in1","max.in1");
    def->connect("self.in2","min.in0");
    def->connect("max.out","min.in1");
    def->connect("self.out","min.out");
  });

  //*** Define abs,absd ***//
  Generator* abs = c->getGenerator("commonlib.abs");
  abs->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    def->addInstance("out_mux","coreir.mux",args);
    def->addInstance("is_pos","coreir.sge",args);
    def->addInstance("mult","coreir.mul",args);

    def->addInstance("negone_const",
		     "coreir.const",
		     {{"width",Const::make(c,width)}},
		     {{"value", Const::make(c, width, -1)}});
    def->addInstance("zero_const",
		     "coreir.const",
		     {{"width",Const::make(c, width)}},
		     {{"value", Const::make(c, width, 0)}});

    // is_pos = in > 0
    def->connect("self.in","is_pos.in0");
    def->connect("zero_const.out","is_pos.in1");

    // in * -1
    def->connect("negone_const.out","mult.in0");
    def->connect("self.in","mult.in1");

    // is_pos ? in : -in
    def->connect("is_pos.out","out_mux.sel");
    def->connect("self.in","out_mux.in1");
    def->connect("mult.out","out_mux.in0");

    def->connect("out_mux.out","self.out");
  });

  Generator* absd = c->getGenerator("commonlib.absd");
  absd->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("abs","commonlib.abs",args);
    def->addInstance("sub","coreir.sub",args);

    def->connect("self.in0","sub.in0");
    def->connect("self.in1","sub.in1");
    def->connect("sub.out","abs.in");
    def->connect("abs.out","self.out");
  });

  //*** Define iterative divider ***//
  //Generator* div = c->getGenerator("commonlib.div");
  // TODO: implement divider
  
  //*** Define MAD ***//
  Generator* MAD = c->getGenerator("commonlib.MAD");
  MAD->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("mult","coreir.mul",args);
    def->addInstance("add","coreir.add",args);

    def->connect("self.in0","mult.in0");
    def->connect("self.in1","mult.in1");
    def->connect("self.in2","add.in0");
    def->connect("mult.out","add.in1");
    def->connect("add.out", "self.out");
  });


  //*** Define demux2 ***//
  // TODO: implement demux
  
  
  

  ///////////////////////////////////
  //*** const array definition  ***//
  ///////////////////////////////////

  Params const_array_args =  {{"type",CoreIRType::make(c)},{"value",c->Int()}};
  TypeGen* constArrayTG = coreirprims->newTypeGen(
    "constArrayTG",
    const_array_args,
    [](Context* c, Values args) {
      Type* t = args.at("type")->get<Type*>();

      RecordParams r({
          {"out", t}
        });
      return c->Record(r);
    }
  );
  Generator* const_array = commonlib->newGeneratorDecl("const_array",constArrayTG,const_array_args);
  const_array->addDefaultGenArgs({{"value",Const::make(c,0)}});

  const_array->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      Type* type = args.at("type")->get<Type*>();
      int value = args.at("value")->get<int>();
      Type* cType = type;

      // identify type size
      vector<uint> lengths;
      uint bitwidth = 1;
      while(!cType->isBaseType()) {
        assert(cType->getKind() == Type::TypeKind::TK_Array);
        ArrayType* aType = static_cast<ArrayType*>(cType);
        uint length = aType->getLen();
        
        cType = aType->getElemType();
        if (cType->isBaseType()) {
          bitwidth = length;
        } else {
          //lengths.insert(lengths.begin(), length);
          lengths.push_back(length);
        }
      }

      // create and connect the interface
      Wireable* pt_out = def->addInstance("pt_out", "mantle.wire", {{"type",Const::make(c,type)}});
      def->connect("self.out", "pt_out.out");

      // collect all interface wires
      std::vector<Wireable*> out_wires; out_wires.push_back(pt_out->sel("in"));
      for (uint dim_length : lengths) {
        std::vector<Wireable*> out_temp;
        out_temp.reserve(out_wires.size() * dim_length);

        for (uint i=0; i<dim_length; ++i) {
          for (auto out_wire : out_wires) {
            out_temp.push_back(out_wire->sel(i));
          }
        }
        out_wires = out_temp;
      }

      // create and wire up constants
      for (uint i=0; i<out_wires.size(); ++i) {
        std::string const_name = "const_" + std::to_string(i);
        Values const_args = {{"width", Const::make(c,bitwidth)}};

        Values const_configargs = {{"value", Const::make(c,BitVector(bitwidth,value))}};
        Wireable* const_inst = def->addInstance(const_name, "coreir.const", const_args, const_configargs);
        def->connect(const_inst->sel("out"), out_wires[i]);
      }

    });

  /////////////////////////////////
  //*** reg array definition  ***//
  /////////////////////////////////

  Params reg_array_args =  {{"type",CoreIRType::make(c)},{"has_en",c->Bool()},{"has_clr",c->Bool()},{"has_rst",c->Bool()},{"init",c->Int()}};
  TypeGen* regArrayTG = coreirprims->newTypeGen(
    "regArrayTG",
    reg_array_args,
    [](Context* c, Values args) {
      Type* t = args.at("type")->get<Type*>();
      bool en  = args.at("has_en")->get<bool>();
      bool clr = args.at("has_clr")->get<bool>();
      bool rst = args.at("has_rst")->get<bool>();
      assert(!(clr && rst));

      RecordParams r({
          {"in", t->getFlipped()},
          {"clk", c->Named("coreir.clkIn")},
          {"out", t}
        });
      if (en) r.push_back({"en",c->BitIn()});
      if (clr) r.push_back({"clr",c->BitIn()});
      if (rst) r.push_back({"rst",c->BitIn()});
      return c->Record(r);
    }
  );
  Generator* reg_array = commonlib->newGeneratorDecl("reg_array",regArrayTG,reg_array_args);
  reg_array->addDefaultGenArgs({{"has_en",Const::make(c,false)},{"has_clr",Const::make(c,false)},{"has_rst",Const::make(c,false)},{"init",Const::make(c,0)}});

  reg_array->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      Type* type = args.at("type")->get<Type*>();
      bool en = args.at("has_en")->get<bool>();
      bool clr = args.at("has_clr")->get<bool>();
      bool rst = args.at("has_rst")->get<bool>();
      int init = args.at("init")->get<int>();
      Type* cType = type;

      // identify type size
      vector<uint> lengths;
      uint bitwidth = 1;
      while(!cType->isBaseType()) {
        assert(cType->getKind() == Type::TypeKind::TK_Array);
        ArrayType* aType = static_cast<ArrayType*>(cType);
        uint length = aType->getLen();
        
        cType = aType->getElemType();
        if (cType->isBaseType()) {
          bitwidth = length;
        } else {
          //lengths.insert(lengths.begin(), length);
          lengths.push_back(length);
        }
      }

      // create and connect the interface
      Wireable* pt_in = def->addInstance("pt_in", "mantle.wire", {{"type",Const::make(c,type)}});
      Wireable* pt_out = def->addInstance("pt_out", "mantle.wire", {{"type",Const::make(c,type)}});
      def->connect("self.in", "pt_in.in");
      def->connect("self.out", "pt_out.out");

      // collect all interface wires
      std::vector<Wireable*> in_wires; in_wires.push_back(pt_in->sel("out"));
      std::vector<Wireable*> out_wires; out_wires.push_back(pt_out->sel("in"));
      for (uint dim_length : lengths) {
        std::vector<Wireable*> in_temp; 
        std::vector<Wireable*> out_temp;
        in_temp.reserve(in_wires.size() * dim_length);
        out_temp.reserve(out_wires.size() * dim_length);

        for (uint i=0; i<dim_length; ++i) {
          for (auto in_wire : in_wires) {
            in_temp.push_back(in_wire->sel(i));
          }
          for (auto out_wire : out_wires) {
            out_temp.push_back(out_wire->sel(i));
          }
        }
        in_wires = in_temp;
        out_wires = out_temp;
      }

      // create and wire up registers
      assert(in_wires.size() == out_wires.size());
      for (uint i=0; i<in_wires.size(); ++i) {
        std::string reg_name = "reg_" + std::to_string(i);
        Values reg_args = {{"width", Const::make(c,bitwidth)},
                           {"has_en", Const::make(c,en)},
                           {"has_clr", Const::make(c,clr)},
                           {"has_rst", Const::make(c,rst)}};
        Values reg_configargs = {{"init", Const::make(c,BitVector(bitwidth,init))}};
        Wireable* reg = def->addInstance(reg_name, "mantle.reg", reg_args, reg_configargs);
        if (en) { def->connect("self.en", reg_name+".en"); }
        if (clr) { def->connect("self.clr", reg_name+".clr"); }
        if (rst) { def->connect("self.rst", reg_name+".rst"); }
        def->connect(in_wires[i], reg->sel("in"));
        def->connect(reg->sel("out"), out_wires[i]);
      }

    });

 

  /////////////////////////////////
  //*** muxN definition       ***//
  /////////////////////////////////

  Generator* muxN = commonlib->newGeneratorDecl("muxn",commonlib->getTypeGen("muxN_type"),{{"width",c->Int()},{"N",c->Int()}});

  muxN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint N = genargs.at("N")->get<int>();
    assert(N>0);
      Namespace* stdlib = c->getNamespace("coreir");
      Namespace* commonlib = c->getNamespace("commonlib");
      Generator* mux2 = stdlib->getGenerator("mux");
      Generator* muxN = commonlib->getGenerator("muxn");

      Const* aWidth = Const::make(c,width);

      if (N == 1) {
        def->connect("self.in.data.0","self.out");
        def->addInstance("term_sel", "corebit.term");
        def->connect("self.in.sel.0", "term_sel.in");
      }
      else if (N == 2) {
        def->addInstance("_join",mux2,{{"width",aWidth}});
        def->connect("_join.out","self.out");

        def->connect("self.in.data.0","_join.in0");
        def->connect("self.in.data.1","_join.in1");
        def->connect("self.in.sel.0", "_join.sel");
      }
      else {
        def->addInstance("_join",mux2,{{"width",aWidth}});
        def->connect("_join.out","self.out");

        //Connect half instances
        uint Nbits = num_bits(N-1); // 4 inputs has a max index of 3
        uint Nlargehalf = 1 << (Nbits-1);
        uint Nsmallhalf = N - Nlargehalf;

        //cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking into " << Nlargehalf << " and " << Nsmallhalf <<endl;

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

        def->connect("muxN_0.out","_join.in0");
        def->connect("muxN_1.out","_join.in1");

        // wire up selects
        def->connect({"self","in","sel",to_string(Nbits-1)},{"_join","sel"});
        Values sliceArgs0 = {{"width", Const::make(c,Nbits)},
                             {"lo", Const::make(c,0)},
                             {"hi", Const::make(c,num_bits(Nlargehalf-1))}};
        Values sliceArgs1 = {{"width", Const::make(c,Nbits)},
                             {"lo", Const::make(c,0)},
                             {"hi", Const::make(c,num_bits(Nsmallhalf-1))}};

        def->addInstance("sel_slice0", "coreir.slice", sliceArgs0); 
        def->connect("self.in.sel", "sel_slice0.in");
        def->connect("sel_slice0.out", "muxN_0.in.sel");

        def->addInstance("sel_slice1", "coreir.slice", sliceArgs1); 
        def->connect("self.in.sel", "sel_slice1.in");
        def->connect("sel_slice1.out", "muxN_1.in.sel");
      }

    });


  
  /////////////////////////////////
  //*** opN definition        ***//
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
      def->connect("self.in.0","self.out");
    }
    else if (N == 2) {
      def->addInstance("_join",op2,{{"width",aWidth}});
      def->connect("_join.out","self.out");

      def->connect("self.in.0","_join.in0");
      def->connect("self.in.1","_join.in1");
    }
    else {
      def->addInstance("_join",op2,{{"width",aWidth}});
      def->connect("_join.out","self.out");

      //Connect half instances
      uint Nbits = num_bits(N-1); // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits-1);
      uint Nsmallhalf = N - Nlargehalf;

      //cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking into " << Nlargehalf << " and " << Nsmallhalf <<endl;
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
      def->connect("opN_0.out","_join.in0");
      def->connect("opN_1.out","_join.in1");
    }

  });

  /////////////////////////////////
  //*** bitopN definition     ***//
  /////////////////////////////////

  Generator* bitopN = commonlib->newGeneratorDecl("bitopn",commonlib->getTypeGen("bitopN_type"),{{"N",c->Int()},{"operator",c->String()}});

  bitopN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint N = genargs.at("N")->get<int>();
    std::string op2 = genargs.at("operator")->get<string>();
    assert(N>0);

    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* opN = commonlib->getGenerator("bitopn");

    Const* aOperator = Const::make(c,op2);

    if (N == 1) {
      def->connect("self.in.0","self.out");
    }
    else if (N == 2) {
      def->addInstance("_join",op2);
      def->connect("_join.out","self.out");

      def->connect("self.in.0","_join.in0");
      def->connect("self.in.1","_join.in1");
    }
    else {
      def->addInstance("_join",op2);
      def->connect("_join.out","self.out");

      //Connect half instances
      uint Nbits = num_bits(N-1); // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits-1);
      uint Nsmallhalf = N - Nlargehalf;

      //cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking into " << Nlargehalf << " and " << Nsmallhalf <<endl;
      Const* aNlarge = Const::make(c,Nlargehalf);
      Const* aNsmall = Const::make(c,Nsmallhalf);

      def->addInstance("opN_0",opN,{{"N",aNlarge},{"operator",aOperator}});
      def->addInstance("opN_1",opN,{{"N",aNsmall},{"operator",aOperator}});
      for (uint i=0; i<Nlargehalf; ++i) {
        def->connect({"self","in",to_string(i)},{"opN_0","in",to_string(i)});
      }
      for (uint i=0; i<Nsmallhalf; ++i) {
        def->connect({"self","in",to_string(i+Nlargehalf)},{"opN_1","in",to_string(i)});
      }
      def->connect("opN_0.out","_join.in0");
      def->connect("opN_1.out","_join.in1");
    }

  });


  //*** Add a LUTN ***//
  auto LUTModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params p; //params
    Values d; //defaults
    int N = genargs.at("N")->get<int>();
    p["init"] = c->BitVector(1<<N);
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


  //TODO this really should exist in a separate verilog definitions file for commonlib
  //Set verilog for the LutN
  json vjson;
  vjson["parameters"] = {"init"};
  vjson["interface"] = {"input [N-1:0] in","output out"};
  vjson["definition"] = "  assign out = init[in];";
  lutN->getMetaData()["verilog"] = vjson;

  Params MemGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  //*** Linebuffer Memory. Use this for memory in linebuffer mode ***//
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

//// reference verilog code for lbmem
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



  //*** Fifo Memory. Use this for memory in Fifo mode ***//
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

  
  //////////////////////////////////////////////////
  //*** generic recursively defined linebuffer ***//
  //////////////////////////////////////////////////

  // top-level linebuffer that should be used by the user
  Params lb_args = 
    {{"input_type",CoreIRType::make(c)},
     {"output_type",CoreIRType::make(c)},
     {"image_type",CoreIRType::make(c)},
     {"has_valid",c->Bool()},
     {"has_stencil_valid",c->Bool()}
    };

  commonlib->newTypeGen(
    "lb_type", //name for the typegen
    lb_args,
    [](Context* c, Values genargs) { //Function to compute type
      bool has_valid = genargs.at("has_valid")->get<bool>();
      bool has_stencil_valid = genargs.at("has_stencil_valid")->get<bool>();
      Type* in_type  = genargs.at("input_type")->get<Type*>();
      Type* out_type  = genargs.at("output_type")->get<Type*>();
      Type* img_type = genargs.at("image_type")->get<Type*>();

      // can't have has_stencil_valid without a valid
      ASSERT(!(!has_valid && has_stencil_valid),
        "One must have a valid signal to utilize stencil valid");

      // process and check the input arguments
      vector<uint> in_dims = get_dims(in_type);
      vector<uint> out_dims = get_dims(out_type);
      vector<uint> img_dims = get_dims(img_type);

      uint bitwidth = in_dims[0]; // first array is bitwidth
      ASSERT(bitwidth > 0, "The first dimension for the input is interpretted "
             "as the bitwidth which was set to " + to_string(bitwidth));

      ASSERT(bitwidth == out_dims[0], 
             to_string(bitwidth) + " != " + to_string(out_dims[0]) + \
             "all bitwidths must match (input doesn't match output)");
      ASSERT(bitwidth == img_dims[0], 
             to_string(bitwidth) + " != " + to_string(img_dims[0]) + \
             "all bitwidths must match (input doesn't match image)");

      // erase the bitwidth size from vectors
      in_dims.erase(in_dims.begin()); 
      out_dims.erase(out_dims.begin());
      img_dims.erase(img_dims.begin());

      uint num_dims = in_dims.size();
      ASSERT(num_dims == out_dims.size(),
             "all must have same number of dimensions (input and output mismatch)");
      ASSERT(num_dims == img_dims.size(),
             "all must have same number of dimensions (input and image mismatch)");

      // we will check all dimensions for correct construction
      for (uint dim=0; dim<num_dims; ++dim) {
        uint out_dimx = out_dims[dim];
        uint img_dimx = img_dims[dim];
        uint in_dimx = in_dims[dim];

        ASSERT(img_dimx >= out_dimx,
               "image dimension length (" + to_string(img_dimx) + \
               ") must be larger than output (" + to_string(out_dimx) + \
               ") in dim " + to_string(dim));
        ASSERT(out_dimx >= in_dimx,
               "output stencil size (" + to_string(out_dimx) + \
               ") must be larger than input (" + to_string(in_dimx) + \
               ") in dim " + to_string(dim));
        ASSERT(img_dimx % in_dimx == 0,
               "img_dim=" + to_string(img_dimx) + " % in_dim=" + to_string(in_dimx) + \
               " != 0 in dim=" + to_string(dim) + \
               ", dimension length must be divisible, because we can't swizzle data");
        ASSERT(out_dimx % in_dimx == 0,
               "out_dim=" + to_string(out_dimx) + " % in_dim=" + to_string(in_dimx) + \
               " != 0 in dim=" + to_string(dim) + \
               ", dimension length must be divisible, because we can't swizzle data");

        if (img_dimx - out_dimx < 3 && (img_dimx != out_dimx)) {
          std::cout << "Image dimension " << dim << "  is " << img_dimx
                    << " and output stencil size is " << out_dimx
                    << ", which means the linebuffer mem is going to be very small"
                    << std::endl;
      
        }
      }

      // create the ports for the linebuffer
      RecordParams recordparams = {
          {"in", in_type},
          {"reset", c->BitIn()},
          {"wen",c->BitIn()},
          {"out", out_type}
      };

      if (has_valid) { recordparams.push_back({"valid",c->Bit()}); }
      return c->Record(recordparams);
    }
  );

  Generator* lb = commonlib->newGeneratorDecl(
    "linebuffer",
    commonlib->getTypeGen("lb_type"),
    lb_args
  );
  lb->addDefaultGenArgs({{"has_valid",Const::make(c,false)}});
  lb->addDefaultGenArgs({{"has_stencil_valid",Const::make(c,false)}});

  lb->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
      bool has_valid = genargs.at("has_valid")->get<bool>();
      bool has_stencil_valid = genargs.at("has_stencil_valid")->get<bool>();
      bool is_last_lb= true;
      Type* in_type  = genargs.at("input_type")->get<Type*>();
      Type* out_type = genargs.at("output_type")->get<Type*>();
      Type* img_type = genargs.at("image_type")->get<Type*>();

      // create a linebuffer
      Values lb_args = {
            {"input_type", Const::make(c, in_type)},
            {"image_type", Const::make(c, img_type)},
            {"output_type", Const::make(c, out_type)},
            {"has_valid", Const::make(c, has_valid)},
            {"has_stencil_valid", Const::make(c, has_stencil_valid)},
            {"is_last_lb", Const::make(c, is_last_lb)}
      };

      def->addInstance("lb_recurse",
                       "commonlib.linebuffer_recursive",
                       lb_args);

      // connect linebuffer to this generator's ports
      def->connect("self.in", "lb_recurse.in");
      def->connect("self.reset", "lb_recurse.reset");
      def->connect("self.wen", "lb_recurse.wen");
      if (has_valid) {
        def->connect("self.valid", "lb_recurse.valid");
      }

      // flip all of the outputs to the correct output port
      vector<uint> in_dims = get_dims(in_type);
      vector<uint> out_dims = get_dims(out_type);
      vector<uint> img_dims = get_dims(img_type);
      in_dims.erase(in_dims.begin()); 
      out_dims.erase(out_dims.begin());
      img_dims.erase(img_dims.begin());
      uint num_dims = in_dims.size();

      std::vector<std::pair<string,string>> out_pairs;
      out_pairs.push_back({"lb_recurse.out", "self.out"});
      for (int dim=num_dims-1; dim>=0; --dim) {
        uint  inx =  in_dims[dim];
        uint outx = out_dims[dim];

        std::vector<std::pair<string,string>> out_temp;
        out_temp.reserve(out_pairs.size() * outx);
        for (uint i=0; i<outx; ++i) {
          for (auto out_pair : out_pairs) {
            string source = out_pair.first;
            string sink = out_pair.second;
            uint iflip = inverted_index(outx, inx, i);
            out_temp.push_back({source + "." + to_string(i),
                    sink + "." + to_string(iflip)});
            
          }
        }
        out_pairs = out_temp;
      }

      //std::cout << "linebuffer connections:" << std::endl;
      for (auto out_pair : out_pairs) {
        //std::cout << "  connecting " << out_pair.first
        //          << " to " << out_pair.second
        //          << std::endl;
        def->connect(out_pair.first, out_pair.second);
      }
      //std::cout << std::endl;
      
    }
    );


  // recursive version for linebuffer
  Params lb_recursive_args = 
      {{"input_type",CoreIRType::make(c)},
       {"output_type",CoreIRType::make(c)},
       {"image_type",CoreIRType::make(c)},
       {"has_valid",c->Bool()},
       {"has_stencil_valid",c->Bool()},
       {"is_last_lb",c->Bool()} // use this to denote when to create valid register chain
      };

  commonlib->newTypeGen(
      "lb_recursive_type", //name for the typegen
      lb_recursive_args,
      [](Context* c, Values genargs) { //Function to compute type
        bool has_valid = genargs.at("has_valid")->get<bool>();
        //bool is_last_lb = genargs.at("is_last_lb")->get<bool>();
        Type* in_type  = genargs.at("input_type")->get<Type*>();
        Type* out_type  = genargs.at("output_type")->get<Type*>();
        RecordParams recordparams = {
          {"in", in_type},
          {"reset", c->BitIn()},
          {"wen",c->BitIn()},
          {"out", out_type}
        };

        if (has_valid) { recordparams.push_back({"valid",c->Bit()}); }
        if (has_valid) { recordparams.push_back({"valid_chain",c->Bit()}); }
        return c->Record(recordparams);
      }
                        );
  
  Generator* lb_recursive = commonlib->newGeneratorDecl(
      "linebuffer_recursive",
      commonlib->getTypeGen("lb_recursive_type"),
      lb_recursive_args
    );
  
  lb_recursive->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    //cout << "running linebuffer generator" << endl;
    bool has_valid = genargs.at("has_valid")->get<bool>();
    bool has_stencil_valid = genargs.at("has_stencil_valid")->get<bool>();
    bool is_last_lb= genargs.at("is_last_lb")->get<bool>();
    Type* in_type  = genargs.at("input_type")->get<Type*>();
    Type* out_type = genargs.at("output_type")->get<Type*>();
    Type* img_type = genargs.at("image_type")->get<Type*>();
    vector<uint> in_dims = get_dims(in_type);
    vector<uint> out_dims = get_dims(out_type);
    vector<uint> img_dims = get_dims(img_type);

    uint bitwidth = in_dims[0]; // first element in array is bitwidth
    ASSERT(bitwidth > 0, "The first dimension for the input is interpretted "
					 "as the bitwidth which was set to " + to_string(bitwidth));

    // erase the bitwidth size from vectors
    in_dims.erase(in_dims.begin()); 
    out_dims.erase(out_dims.begin());
    img_dims.erase(img_dims.begin());

    // last dimension most commonly used
    uint num_dims = in_dims.size();
    uint dim = num_dims-1;
    uint out_dim = out_dims[dim];
    uint img_dim = img_dims[dim];
    uint in_dim = in_dims[dim];

    if (!is_last_lb) {
      ASSERT(has_valid, "is_last_lb was set to false when !has_valid. This flag should not be used unless using valid output port");
    }

    //cout << "finished a bunch of asserts" << endl;

    string reg_prefix = "reg_";
    Const* aBitwidth = Const::make(c,bitwidth);
    assert(isa<ConstInt>(aBitwidth));

    // NOTE: registers and lbmems named such that they correspond to output connections

    ////////////////////////////////////////////
    ///// BASE CASE: DIM==1, all registers /////
    ////////////////////////////////////////////
    if (num_dims == 1) {
      //cout << "creating base case linebuffer" << endl;
      // connect based on input size
      for (uint i=0; i<out_dim; ++i) {
        // output goes to mirror position, except keeping order within a single clock cycle
        //uint iflip = (out_dim-1) - (in_dim - 1 - i % in_dim) - (i / in_dim) * in_dim;

        //uint iflip = (out_dim-1) - i;
        uint iflip = i;

        // connect to input
        if (i < in_dim) {
          def->connect({"self","in",to_string(i)}, {"self","out",to_string(iflip)});

        // create and connect to register; register connects input
        } else if ((i >= in_dim) && (i < 2*in_dim)) {
          uint in_idx = i - in_dim;
          string reg_name = reg_prefix + to_string(i);
          def->addInstance(reg_name, "coreir.reg", {{"width",aBitwidth}});
          def->connect({"self","in",to_string(in_idx)}, {reg_name, "in"});
          def->connect({reg_name, "out"}, {"self","out",to_string(iflip)});
         
        // create and connect to register; register connects to previous register
        } else {
          uint in_idx = i - in_dim;
          string reg_name = reg_prefix + to_string(i);
          string prev_reg_name = reg_prefix + to_string(in_idx);
          def->addInstance(reg_name, "coreir.reg", {{"width",aBitwidth}});
          def->connect({prev_reg_name, "out"}, {reg_name, "in"});
          def->connect({reg_name, "out"}, {"self","out",to_string(iflip)});

        }
      }


      // create and connect valid chain
      if (has_valid) {
        if (is_last_lb) {
          // this is a chain of valids
          string valid_prefix = "valreg_";

          uint last_idx = -1;
          for (uint i=0; i<out_dim-in_dim; i+=in_dim) {
          
            // connect to input wen
            if (i == 0) {
              string reg_name = valid_prefix + to_string(i);
              def->addInstance(reg_name, "corebit.reg");
              def->connect({"self","wen"}, {reg_name,"in"});
         
              // create and connect to register; register connects to previous register
            } else {
              uint in_idx = i - in_dim;
              string reg_name = valid_prefix + to_string(i);
              string prev_reg_name = valid_prefix + to_string(in_idx);
              def->addInstance(reg_name, "corebit.reg");
              def->connect({prev_reg_name, "out"}, {reg_name, "in"});

            }

            last_idx = i;
          }

          // connect last valid bit to self.valid
          string last_valid_name = valid_prefix + to_string(last_idx);
          def->connect({"self","valid"},{last_valid_name,"out"});
          def->connect({"self","valid_chain"},{last_valid_name,"out"});
        } else {
          def->connect({"self","wen"},{"self","valid"});
          def->connect({"self","wen"},{"self","valid_chain"});
        }
      }  // valid chain
      
      def->addInstance("reset_term", "corebit.term");
      def->connect("self.reset","reset_term.in");

    //////////////////////////  
    ///// RECURSIVE CASE /////
    //////////////////////////  
    } else {
      
      string lb_prefix = "lb" + to_string(dim) + "d_"; // use this for recursively smaller linebuffers
      Type* lb_input = cast<ArrayType>(in_type)->getElemType();
      Type* lb_image = cast<ArrayType>(img_type)->getElemType();
      Type* lb_output = cast<ArrayType>(out_type)->getElemType();

      // recursively create linebuffers
      for (uint i=0; i<out_dim; ++i) {
        string lb_name = lb_prefix + to_string(i);
        //cout << "creating linebuffer named " << lb_name << endl;
        Values args = {
            {"input_type", Const::make(c, lb_input)},
            {"image_type", Const::make(c, lb_image)},
            {"output_type", Const::make(c, lb_output)},
            {"has_valid", Const::make(c, has_valid)},
            {"has_stencil_valid", Const::make(c, has_stencil_valid)},
            {"is_last_lb", Const::make(c, !has_valid)}
          };
        // was used when is_last_lb was used recursively, now only lastlb makes valid counter chain
        //if (!has_valid || (is_last_lb && i == out_dim-1)) { 
        
        def->addInstance(lb_name, "commonlib.linebuffer_recursive", args);
        def->connect({"self","reset"},{lb_name,"reset"});
      }

      // ALL CASES: stencil output connections
      // connect the stencil outupts
      for (uint i=0; i<out_dim; ++i) {
        // output goes to mirror position, except keeping order within a single clock cycle
        //uint iflip = (out_dim-1) - (in_dim-1 - i % in_dim) - (i / in_dim) * in_dim;
        //uint iflip = out_dim-1 - i;
        uint iflip = i;
        string lb_name = lb_prefix + to_string(i);
        
        def->connect({"self","out",to_string(iflip)}, {lb_name,"out"});
      }

      //cout << "created all linebuffers" << endl;
      
      // SPECIAL CASE: same sized stencil output as image, so no lbmems needed (all in regs)
      //if (out_dim == img_dim) {
      if (img_dim == 0) {
        ASSERT(false, "out_dim == img_dim isn't implemented yet");

      } else {
        //cout << "in the regular case of linebuffer" << endl;
 
        // REGULAR CASE: lbmems to store image lines
 
        // create lbmems to store data between linebuffers
        //   size_lbmems = prod((img[x] - (out[x]-in[x])) / in[x]) 
        //      except for x==1, img0 / in0
        uint size_lbmems = 1; //out_dim-1;
        for (uint dim_i=0; dim_i<num_dims-1; dim_i++) {
          if (dim_i == 0) {
            size_lbmems *= img_dims[dim_i] / in_dims[dim_i];
          } else {
            size_lbmems *= img_dims[dim_i] / in_dims[dim_i];
            //size_lbmems *= (img_dims[dim_i] - (out_dims[dim_i]-in_dims[dim_i])) / in_dims[dim_i];
          }
        }

        Const* aLbmemSize = Const::make(c, size_lbmems);

        //   num_lbmems = (prod(in[x]) * (out-in)
        string lbmem_prefix = "lbmem";
        for (uint out_i=0; out_i < out_dim-in_dim; ++out_i) {

          uint num_indices = num_dims - 1;
          //cout << "we have " << num_dims << " dims and " << num_indices << " input dims" << endl;
          uint indices[num_indices];

          memset( indices, 0, num_indices*sizeof(uint) );

          bool create_more_lbmems = true;
          while (create_more_lbmems) {
            ///// create lbmem //////
            
            // create lbmem name (lbmem_x_<in2>_<in1>_<in0>)
            uint lbmem_line = out_i + in_dim;
            string lbmem_name = lbmem_prefix + "_" + to_string(lbmem_line);

            for (int dim_i=num_indices-1; dim_i>=0; --dim_i) {
              lbmem_name += "_" + to_string(indices[dim_i]);
            }

            if (has_stencil_valid) {
              def->addInstance(lbmem_name, "memory.rowbuffer_stencil_valid",
                               {{"width",aBitwidth},{"depth",aLbmemSize},{"stencil_width",Const::make(c, 0)}});

            } else {
              def->addInstance(lbmem_name, "memory.rowbuffer",
                               {{"width",aBitwidth},{"depth",aLbmemSize}});
            }


            // hook up flush
            // FIXME: actually create flush signal using counters
            string lbmem_flush_name = lbmem_name + "_flush";
            def->addInstance(lbmem_flush_name, "corebit.const", {{"value",Const::make(c,false)}});
            def->connect({lbmem_name,"flush"},{lbmem_flush_name,"out"});

            ///// connect lbmem input and wen /////
            //cout << "connecting lbmem input for " << lbmem_name << endl;
            string input_name, input_suffix;
            string delim;
            if (num_dims == 2) { // special case with a 2D linebuffer
              // connect to input or end of last lbmem
              if (out_i < in_dim) {
                input_name = "self.in." + to_string(out_i);
                delim = ".";
                input_suffix = "";

              } else {
                // connect lbmem from previous line
                input_name = lbmem_prefix + "_" + to_string(lbmem_line-in_dim);
                delim = "_";
                input_suffix = ".rdata";
              }

              for (int dim_i=num_indices-1; dim_i>=0; --dim_i) {
                input_name += delim + to_string(indices[dim_i]);
              }

              def->connect(input_name + input_suffix, lbmem_name + ".wdata");

              // connect wen
              if (has_valid) {
                 if (out_i < in_dim) {
                   // use self wen; actually stall network for now
                   def->connect("self.wen", lbmem_name + ".wen");

                 } else {
                   // use valid from previous lbmem
                   def->connect(input_name + ".valid", lbmem_name + ".wen");
                 }
              } else {
                def->connect("self.wen", lbmem_name + ".wen");
              }

            } else {
              ///// connect lbmem inputs for non-2d case /////
              // connect to end of associated linebuffer, which is one of the stencil outputs
              input_name = lb_prefix + to_string(out_i) + ".out";
              for (int dim_i=num_indices-1; dim_i>=0; --dim_i) {
                if (dim_i == 0) {
                  // for last dimension, don't go to the end of register chain
                  uint index_i = inverted_index(out_dims[dim_i], in_dims[dim_i], indices[dim_i]);
                  input_name += "." + to_string(index_i);
                } else {
                  input_name += "." + to_string(in_dims[dim_i]-1 - indices[dim_i]);
                }
              }
              def->connect(lbmem_name + ".wdata", input_name);

              // connect wen if has_valid
              if (has_valid) {
                 if (out_i < in_dim) {
                   // use self wen; actually stall network for now
                   def->connect("self.wen", lbmem_name + ".wen");

                 } else {
                   // use valid from previous lbmem
                   def->connect(input_name + ".valid_chain", lbmem_name + ".wen");
                 }
              } else {
                def->connect("self.wen", lbmem_name + ".wen");
              }

            }

            //cout << "connecting lbmem output" << endl;
            ///// connect lbmem output /////
            // connect the lbmem output to linebuffer input in next layer
            string output_base = lb_prefix + to_string(out_i+in_dim);
            string output_name = output_base + ".in";
            for (int dim_i=num_indices-1; dim_i>=0; --dim_i) {
              output_name += "." + to_string(indices[dim_i]);
            }
            def->connect(lbmem_name + ".rdata", output_name);

            // increment lbmem indices
            indices[0] += 1;
            for (uint dim_i=0; dim_i<num_indices; dim_i++) {
              if (indices[dim_i] >= in_dims[dim_i]) {
                if ((uint)dim_i == num_dims-2) {
                  create_more_lbmems = false;
                } else {
                  indices[dim_i+1] += 1;
                  indices[dim_i] = 0;
                }
              }
            } // indices increment
            
          } // while create_more_lbmems
        } // for out_i

        //cout << "connecting linbuffer inputs" << endl;
        // connect linebuffer inputs to input (other already connected to lbmems)
        for (uint out_i=0; out_i<in_dim; ++out_i) {
          string lb_name = lb_prefix + to_string(out_i);
          def->connect({"self","in",to_string(out_i)}, {lb_name, "in"});
        }

        ///// connect linebuffer outputs /////
        if (has_valid) {
					// check if we create lbmems or not
					string valid_chain_str;
					if (out_dim - in_dim > 0) {
						// use the last lbmem for valid chaining (note this signal is duplicated among all in_dims)
						//  recall lbmem naming: lbmem_x_<in2>_<in1>_<in0>
						string last_lbmem_name = lbmem_prefix;
						for (int dim_i=num_dims-1; dim_i>=0; dim_i--) {
							if (dim_i == (int)(num_dims-1)) {
								last_lbmem_name += "_" + to_string(out_dim-1);
							} else {
								last_lbmem_name += "_" + to_string(in_dims[dim_i]-1);
							}
						}
						valid_chain_str = last_lbmem_name + ".valid";
					} else {
						valid_chain_str = "self.wen";
					}
					def->connect(valid_chain_str, "self.valid_chain");

          // create counters to create valid output (if top-level linebuffer)
          if (is_last_lb == false) {
            def->connect(valid_chain_str, "self.valid");
            def->addInstance("reset_term", "corebit.term");
            def->connect("self.reset","reset_term.in");
          } else if (is_last_lb && !has_stencil_valid) {

            std::vector<std::string> counter_outputs;
            counter_outputs.push_back("self.wen");
            
            // create a counter for every dimension
            for (uint dim_i=0; dim_i<num_dims; dim_i++) {
            //for (int dim_i=num_dims-1; dim_i>=0; dim_i--) {
              // comparator for valid (if stencil_size-1 <= count)
              int const_value = (out_dims[dim_i] / in_dims[dim_i]) - 1;
              //FIXME: not implemented, because overflow needed to trigger next counter
              //if (const_value == 0) continue;  // no counter needed if stencil_size is 1

              string const_name = "const_stencil" + to_string(dim_i);
              Values const_arg = {{"value",Const::make(c,BitVector(bitwidth,const_value))}};
              def->addInstance(const_name, "coreir.const", {{"width",aBitwidth}}, const_arg);

              string compare_name = "valcompare_" + to_string(dim_i);
              def->addInstance(compare_name,"coreir.ule",{{"width",aBitwidth}});

              // counter
              string counter_prefix = "valcounter_";
              string counter_name = counter_prefix + to_string(dim_i);
              Values counter_args = {
                {"width",Const::make(c,bitwidth)},
                {"min",Const::make(c,0)},
                {"max",Const::make(c,img_dims[dim_i] / in_dims[dim_i] - 1)},
                {"inc",Const::make(c,1)}
              };
              def->addInstance(counter_name,"commonlib.counter",counter_args);

              // connect reset to 0
              def->connect({counter_name, "reset"},{"self","reset"});

              // connections
              // counter en by wen or overflow bit
              //if (dim_i == 0 || counter_outputs.size() == 1) {
              if (dim_i == 0 || counter_outputs.size() == 1) {
                //def->connect({last_lbmem_name,"valid"},{counter_name,"en"});
                def->connect("self.wen",counter_name + ".en");
              } else {
                string last_compare_out_name = counter_outputs[counter_outputs.size()-1];
                string last_compare_name = last_compare_out_name.substr(0, last_compare_out_name.find(".out"));
                string last_compare_index = last_compare_name.substr(last_compare_name.find("_")+1);
                string last_counter_name = counter_prefix + last_compare_index;
                def->connect({last_counter_name,"overflow"},{counter_name,"en"});
              }

              // wire up comparator
              def->connect({const_name,"out"},{compare_name,"in0"});
              def->connect({counter_name,"out"},{compare_name,"in1"});
              counter_outputs.push_back(compare_name + ".out");
              //std::cout << "counter" << dim_i << " counts to " << const_value << std::endl;
              //def->connect({compare_name,"out"},{andr_name,"in",to_string(dim_i)});
            }

            if (counter_outputs.size() == 0) {
              def->connect("self.wen", "self.valid");
              def->addInstance("reset_term", "corebit.term");
              def->connect("self.reset","reset_term.in");

            } else {
              // andr all comparator outputs
              string andr_name = "valid_andr";
              Values andr_params = {{"N",Const::make(c,counter_outputs.size())},
                                    {"operator",Const::make(c,"corebit.and")}};
              def->addInstance(andr_name,"commonlib.bitopn",andr_params);
              def->connect({andr_name,"out"},{"self","valid"});
              //def->hasConnection({andr_name,"out"},{"self","valid"});

              for (uint dim_i=0; dim_i<counter_outputs.size(); ++dim_i) {
                def->connect(counter_outputs[dim_i], andr_name +".in."+to_string(dim_i));
              }
            }
            
          } else { //if (is_last_lb && has_stencil_valid) {
            ASSERT(is_last_lb && has_stencil_valid,
                   "This should be the only case left if these conditionals are correct");
            
            // By setting the stencil_width on the rowbuffer correctly, we don't need external counters.
            def->connect(valid_chain_str, "self.valid");
          }

        } else { // has_valid == 0
          // hook up wen for rest of linebuffers
          for (uint out_i=in_dim; out_i<out_dim; ++out_i) {
            //string lb_name = lb_prefix + to_string(out_i);
            //def->connect({"self","wen"}, {lb_name, "wen"}); // use stall network
          }
        }

        for (uint out_i=0; out_i<out_dim; ++out_i) {
          string lb_name = lb_prefix + to_string(out_i);
          def->connect({"self","wen"}, {lb_name, "wen"}); // use stall network
        }

        
      } // regular case

    }
    });


  /////////////////////////////////////
  //*** unified buffer definition ***//
  /////////////////////////////////////

  Params ubparams = Params({
      {"width",c->Int()},
      {"depth",c->Int()},
      {"rate_matched",c->Bool()},
      {"stencil_width",c->Int()},
      {"iter_cnt",c->Int()},
      {"num_input_ports",c->Int()},
      {"num_output_ports",c->Int()},
      {"dimensionality",c->Int()},
      {"stride_0",c->Int()},
      {"range_0",c->Int()},
      {"stride_1",c->Int()},
      {"range_1",c->Int()},
      {"stride_2",c->Int()},
      {"range_2",c->Int()},
      {"stride_3",c->Int()},
      {"range_3",c->Int()},
      {"stride_4",c->Int()},
      {"range_4",c->Int()},
      {"stride_5",c->Int()},
      {"range_5",c->Int()},
      {"input_stride_0",c->Int()},
      {"input_range_0",c->Int()},
      {"input_stride_1",c->Int()},
      {"input_range_1",c->Int()},
      {"input_stride_2",c->Int()},
      {"input_range_2",c->Int()},
      {"input_stride_3",c->Int()},
      {"input_range_3",c->Int()},
      {"input_stride_4",c->Int()},
      {"input_range_4",c->Int()},
      {"input_stride_5",c->Int()},
      {"input_range_5",c->Int()},
      {"chain_en",c->Bool()},
      {"chain_idx",c->Int()},
      {"input_starting_addrs",c->Json()},
      {"output_starting_addrs",c->Json()},
      {"logical_size",c->Json()},
      {"init",c->Json()}
    });
  
  // unified buffer type
  commonlib->newTypeGen(
    "unified_buffer_type", //name for the typegen
    ubparams, //generator parameters
    [](Context* c, Values genargs) { //Function to compute type
      uint width = genargs.at("width")->get<int>();
      uint num_inputs = genargs.at("num_input_ports")->get<int>();
      uint num_outputs = genargs.at("num_output_ports")->get<int>();

      RecordParams recordparams = {
        {"wen",c->BitIn()},
        {"ren",c->BitIn()},
        {"flush", c->BitIn()},
        {"reset", c->BitIn()},
        {"valid",c->Bit()}
      };

      // Add the dataports. The simulator needs them to be flattened
      bool simulation_compatible = true;
      if (simulation_compatible) {
        for (size_t i=0; i < num_inputs; ++i) {
          recordparams.push_back({"datain"+std::to_string(i), c->BitIn()->Arr(width)});
        }
        for (size_t i=0; i < num_outputs; ++i) {
          recordparams.push_back({"dataout"+std::to_string(i), c->Bit()->Arr(width)});
        }
      } else {
        recordparams.push_back({"datain",c->BitIn()->Arr(width)->Arr(num_inputs)});
        recordparams.push_back({"dataout",c->Bit()->Arr(width)->Arr(num_outputs)});
      }

      return c->Record(recordparams);
    }
  );

  auto unified_buffer_gen = commonlib->newGeneratorDecl("unified_buffer",commonlib->getTypeGen("unified_buffer_type"),ubparams);
  Json jdata;
  jdata["init"][0] = 0; // set default init to "0"
  unified_buffer_gen->addDefaultGenArgs({{"init",Const::make(c,jdata)}});
  unified_buffer_gen->addDefaultGenArgs({{"stride_1",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"range_1",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"stride_2",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"range_2",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"stride_3",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"range_3",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"stride_4",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"range_4",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"stride_5",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"range_5",Const::make(c,0)}});

  unified_buffer_gen->addDefaultGenArgs({{"input_stride_0",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_range_0",Const::make(c,1)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_stride_1",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_range_1",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_stride_2",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_range_2",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_stride_3",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_range_3",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_stride_4",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_range_4",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_stride_5",Const::make(c,0)}});
  unified_buffer_gen->addDefaultGenArgs({{"input_range_5",Const::make(c,0)}});

  // set default as a single input and output at index 0
  Json jinputs;
  Json joutputs;
  jinputs["input_start"][0] = 0;
  joutputs["output_start"][0] = 0;
  unified_buffer_gen->addDefaultGenArgs({{"input_starting_addrs",Const::make(c,jinputs)}});
  unified_buffer_gen->addDefaultGenArgs({{"output_starting_addrs",Const::make(c,joutputs)}});
  unified_buffer_gen->addDefaultGenArgs({{"num_input_ports",Const::make(c,1)}});
  unified_buffer_gen->addDefaultGenArgs({{"num_output_ports",Const::make(c,1)}});

      
  //////////////////////////////////////////////
  //*** abstract unified buffer definition ***//
  //////////////////////////////////////////////
  Params aubparams = 
    {
     {"input_ports", CoreIRType::make(c)},
     {"output_ports", CoreIRType::make(c)},
     {"capacity", CoreIRType::make(c)},
     {"range", CoreIRType::make(c)},
     {"dim_ref", CoreIRType::make(c)},
     {"stride", CoreIRType::make(c)}
    };

    commonlib->newTypeGen(
      "abstract_unified_buffer_type",
      aubparams,
      [](Context* c, Values genargs) { //Function to compute type
      Type* input_port = genargs.at("input_ports")->get<Type*>();
      Type* output_port = genargs.at("output_ports")->get<Type*>();
      
      return c->Record({
        {"wen",c->BitIn()},
        {"ren",c->BitIn()},
        {"flush", c->BitIn()},
        {"reset", c->BitIn()},
        {"in",input_port},
        {"valid",c->Bit()},
        {"out",output_port}
      });
    }
  );
    
  Generator* aub = commonlib->newGeneratorDecl("abstract_unified_buffer",commonlib->getTypeGen("abstract_unified_buffer_type"),aubparams);
  aub->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    });

  /////////////////////////////////
  //*** counter definition    ***//
  /////////////////////////////////

  // counter follows a for loop of format:
  //   for ( int i = $min ; $min <= $max ; i += $inc )
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
        {"reset", c->BitIn()},
        {"out",c->Bit()->Arr(width)},
        {"overflow",c->Bit()}
      });
    }
  );

  //commonlib->newGeneratorDecl("counter",commonlib->getTypeGen("counter_type"),{{"width",c->Int()},{"min",c->Int()},{"max",c->Int()},{"inc",c->Int()}});
  Generator* counter = commonlib->newGeneratorDecl("counter",commonlib->getTypeGen("counter_type"),{{"width",c->Int()},{"min",c->Int()},{"max",c->Int()},{"inc",c->Int()}});
  counter->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint max = genargs.at("max")->get<int>();
    uint min = genargs.at("min")->get<int>();
    uint inc = genargs.at("inc")->get<int>();
    assert(width>0);
    if (max == min) {
      def->addInstance("count_const",
                       "coreir.const",
                       {{"width",Const::make(c, width)}},
                       {{"value", Const::make(c, width, max)}});
      def->addInstance("one_const",
                       "corebit.const",
                       {{"value", Const::make(c, true)}});

      def->connect("self.out", "count_const.out");
      def->connect("self.overflow", "one_const.out");
    } else {
    
      ASSERT(max>min, "max is " + to_string(max) + " while min is " + to_string(min));
  
      // get generators
      Namespace* coreirprims = c->getNamespace("coreir");
      Generator* ult_gen = coreirprims->getGenerator("ult");
      Generator* add_gen = coreirprims->getGenerator("add");
      Generator* const_gen = coreirprims->getGenerator("const");
  
      // create hardware
      Const* aBitwidth = Const::make(c,width);
      Const* aReset = Const::make(c,BitVector(width,min));
      def->addInstance("count", "mantle.reg", {{"width",aBitwidth},{"has_clr",Const::make(c,true)},{"has_en",Const::make(c,true)}},
                       {{"init",aReset}});
  
      def->addInstance("max", const_gen, {{"width",aBitwidth}}, {{"value",Const::make(c,BitVector(width,max))}});
      def->addInstance("inc", const_gen, {{"width",aBitwidth}}, {{"value",Const::make(c,BitVector(width,inc))}});
      def->addInstance("ult", ult_gen, {{"width",aBitwidth}});
      def->addInstance("add", add_gen, {{"width",aBitwidth}});
      def->addInstance("and", "corebit.and");
      def->addInstance("resetOr", "corebit.or");
  
      // wire up modules
      // clear if max < count+inc && en == 1
      def->connect("count.out","self.out");
      def->connect("count.out","add.in0");
      def->connect("inc.out","add.in1");
  
      def->connect("self.en","count.en");
      def->connect("add.out","count.in");
  
      def->connect("add.out","ult.in1");
      def->connect("max.out","ult.in0");

      def->connect("ult.out","and.in0");
      def->connect("self.en","and.in1");
      // and.out === (max < count+inc  &&  en == 1)
      
      // clear count on either getting to max or reset
      def->connect("and.out","resetOr.in0");
      def->connect("self.reset","resetOr.in1");
      def->connect("resetOr.out","count.clr");
      def->connect("and.out","self.overflow");
    }
  });

  /////////////////////////////////
  //*** serializer definition ***//
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
        {"reset",c->BitIn()},
        {"count",c->Bit()->Arr(width)},
        {"ready", c->Bit()}, // have cycled through all outputs, put new inputs on this cycle
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
    assert(width > num_bits(rate-1)); // not enough bits in counter for rate

    // get generators
    Namespace* coreirprims = c->getNamespace("coreir");
    Generator* const_gen = coreirprims->getGenerator("const");
    Generator* eq_gen = coreirprims->getGenerator("eq");

    // create hardware
    Const* aBitwidth = Const::make(c,width);
    def->addInstance("counter", "commonlib.counter",
                     {{"width",aBitwidth},{"min",Const::make(c,0)},{"max",Const::make(c,rate-1)},{"inc",Const::make(c,1)}});
    def->addInstance("muxn", "commonlib.muxn",
                     {{"width",aBitwidth},{"N",Const::make(c,rate)}});
    def->addInstance("equal", eq_gen,
                     {{"width",aBitwidth}});
    def->addInstance("zero", const_gen,
                     {{"width",aBitwidth}},{{"value",Const::make(c,BitVector(width,0))}});
    Values sliceArgs = {{"width", Const::make(c,width)},
                        {"lo", Const::make(c,0)},
                        {"hi", Const::make(c,num_bits(rate-1))}};
    def->addInstance("slice", "coreir.slice", sliceArgs);
    
    // all but input0 are stored in registers
    for (uint i=1; i<rate; ++i) {
      std::string reg_name = "reg_" + std::to_string(i);
      def->addInstance(reg_name, "mantle.reg",
                       {{"width",aBitwidth},{"has_en",Const::make(c,true)}},
                       {{"init", Const::make(c, width, 0)}});
    }
    def->addInstance("ignoreOverflow", "corebit.term");

    // wire up modules
    def->connect("self.reset", "counter.reset");
    def->connect("equal.out", "self.ready");
    def->connect("self.en","counter.en");
    def->connect("counter.out","self.count");
    def->connect("counter.overflow", "ignoreOverflow.in");

    def->connect("counter.out","slice.in");
    def->connect("slice.out","muxn.in.sel");

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
  // deserializer definition     //
  /////////////////////////////////

  // on every cycle, input<n> is received where n=count
  // on count==rate-1, output all input values.


  // serializer type
  commonlib->newTypeGen(
    "deserializer_type", //name for the typegen
    {{"width",c->Int()},{"rate",c->Int()}}, //generater parameters
    [](Context* c, Values args) { //Function to compute type
      uint width = args.at("width")->get<int>();
      uint rate  = args.at("rate")->get<int>();
      return c->Record({
        {"en",c->BitIn()},
        {"reset",c->BitIn()},
        {"valid", c->Bit()}, // output is valid
        {"in",c->BitIn()->Arr(width)},
        {"out",c->Bit()->Arr(width)->Arr(rate)}
      });
    }
  );

  Generator* deserializer = commonlib->newGeneratorDecl("deserializer",commonlib->getTypeGen("deserializer_type"),{{"width",c->Int()},{"rate",c->Int()}});

  deserializer->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    uint rate  = args.at("rate")->get<int>();
    assert(width>0);
    assert(rate>1);

    // create hardware
    Const* aBitwidth = Const::make(c,width);
    for (uint i=0; i<rate-1; ++i) {
      std::string reg_name = "reg_" + std::to_string(i);
      def->addInstance(reg_name, "mantle.reg",
                       {{"width",aBitwidth},{"has_en",Const::make(c,true)}},
                       {{"init", Const::make(c, width, 0)}});
    }
    // these registers pass along the signal to write to one register
    // this signal is initalized by reset being passed in, and is passed along
    // so that only 1 register is written to in each clock cycle
    // and all reg enables after first with not reset so that, if one reset
    // before an earlier one finishes, the earlier one is aborted
    // the first reg starts with signal 1, the rest with 0
    for (uint i=0; i<rate-1; ++i) {
      std::string reg_name = "en_reg_" + std::to_string(i);
      std::string and_name = "en_and_" + std::to_string(i);
      def->addInstance(reg_name, "mantle.reg", {
              {"width",Const::make(c,1)},
              {"has_en",Const::make(c,true)}
          }, {{"init",Const::make(c, 1, i == 0 ? 1 : 0)}});
      def->addInstance(and_name, "corebit.and");
    }
    // this reg is 1 only cycle after last enable reg is 1, to indicate that all registers have been written
    // to in the last cycle
    def->addInstance("validReg", "mantle.reg",
                     {{"width",Const::make(c,1)},{"has_en",Const::make(c,false)}},
                     {{"init", Const::make(c, 1, 0)}});
    // use this for driving input to first enable reg
    def->addInstance("firstEnabledOr", "corebit.or");
    // the not to invert the reset
    def->addInstance("resetInvert", "corebit.not");

    def->connect("self.reset", "resetInvert.in");

    // wire up one input to all regs
    for (uint i=0; i<rate-1; ++i) {
      std::string idx = std::to_string(i);
      std::string reg_name = "reg_"+idx;
      std::string en_reg_name = "en_reg_"+idx;
      std::string en_and_name = "en_and_"+idx;
      std::string next_en_reg_name = "en_reg_"+std::to_string(i+1);

      def->connect("self.in", reg_name+".in");
      def->connect(reg_name+".out", "self.out."+idx);

      // for every data reg, wire in the enable reg
      def->connect(en_reg_name + ".out.0", reg_name + ".en");
      def->connect("self.en", en_reg_name + ".en");

      // if this is the last reg, wire it's output and the deserializer reset into the input for the
      // first enable reg as if either occurs its a reason for starting cycle again
      if (i == rate - 2) {
          def->connect("self.reset", "firstEnabledOr.in0");
          def->connect(en_reg_name + ".out.0", "firstEnabledOr.in1");
          def->connect("firstEnabledOr.out", "en_reg_" + std::to_string(0) + ".in.0");

          // wire up the valid signal, which comes one clock after the last reg is enabled, same cycle
          // as that reg starts emitting the right value
          def->connect(en_reg_name + ".out.0", en_and_name + ".in0");
          def->connect("resetInvert.out", en_and_name + ".in1");
          def->connect(en_and_name + ".out", "validReg.in.0");
          def->connect("validReg.out.0", "self.valid");
      }
      else {
          def->connect(en_reg_name + ".out.0", en_and_name + ".in0");
          def->connect("resetInvert.out", en_and_name + ".in1");
          def->connect(en_and_name + ".out", next_en_reg_name + ".in.0");
      }
    }
    // wire the input to the last output slot, as directly sending that one out so each cycle is
    // 4 clocks, 3 clock ticks
    def->connect("self.in", "self.out." + to_string(rate-1));
  });


  /////////////////////////////////
  //*** decoder definition    ***//
  /////////////////////////////////

  // on count==0, read in all input values.
  // on every cycle, input<n> is outputted where n=count

  // Not yet implemented

  /////////////////////////////////
  //*** reshape definition    ***//
  /////////////////////////////////
  Params reshape_params = 
    {
     {"input_type", CoreIRType::make(c)},
     {"output_type", CoreIRType::make(c)},
    };

  commonlib->newTypeGen(
    "reshape_type",
    reshape_params,
    [](Context* c, Values genargs) { //Function to compute type
      Type* input_type = genargs.at("input_type")->get<Type*>();
      Type* output_type = genargs.at("output_type")->get<Type*>();

      // check that the vectors have the same bitwidth
      auto input_vector = get_dims(input_type);
      auto output_vector = get_dims(output_type);
      assert(input_vector.at(0) == output_vector.at(0));

      // check that the number of elements in each are the same
      int num_inputs = 1;
      int num_outputs = 1;
      for (const auto& input_value : input_vector) {
        num_inputs *= input_value;
      }
      for (const auto& output_value : output_vector) {
        num_outputs *= output_value;
      }
      assert(num_inputs == num_outputs);
      
      return c->Record({
          {"in",input_type},
          {"out",output_type}
        });
    }
    );

  Generator* reshape = commonlib->newGeneratorDecl("reshape",
                                                   commonlib->getTypeGen("reshape_type"),
                                                   reshape_params);
  reshape->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    auto input_type = genargs.at("input_type")->get<Type*>();
    auto output_type = genargs.at("output_type")->get<Type*>();

    auto input_vector = get_dims(input_type);
    auto output_vector = get_dims(output_type);

    // remove the first dimension (bitwidth)
    input_vector.erase(input_vector.begin());
    output_vector.erase(output_vector.begin());

    int num_inputs = 1;
    for (const auto& input_value : input_vector) {
      num_inputs *= input_value;
    }

    vector<uint> input_idxs(input_vector.size());
    vector<uint> output_idxs(output_vector.size());
    
    for (int idx = 0; idx < num_inputs; ++idx) {
      // create input and output port names
      string input_name = "self.in";
      //for (const auto& input_port : input_idxs) {
      for (int i=input_idxs.size()-1; i >= 0; --i) {
        assert(i < (int)input_idxs.size());
        auto input_port = input_idxs.at(i);
        input_name += "." + std::to_string(input_port);
      }
      string output_name = "self.out";
      //for (const auto& output_port : output_idxs) {
      for (int i=output_idxs.size()-1; i >= 0; --i) {
        assert(i < (int)output_idxs.size());
        auto output_port = output_idxs.at(i);
        output_name += "." + std::to_string(output_port);
      }
      def->connect(input_name, output_name);
      
      // increment input index
      input_idxs.at(0) += 1;
      for (size_t dim = 0; dim < input_idxs.size(); ++dim) {
        if (input_idxs.at(dim) >= input_vector.at(dim)) {
          input_idxs.at(dim) = 0;
          if (dim + 1 < input_idxs.size()) {
            input_idxs.at(dim+1) += 1;
          }
        }
      }

      // increment output index
      output_idxs.at(0) += 1;
      for (size_t dim = 0; dim < output_idxs.size(); ++dim) {
        if (output_idxs.at(dim) >= output_vector.at(dim)) {
          output_idxs.at(dim) = 0;
          if (dim + 1 < output_idxs.size()) {
            output_idxs.at(dim+1) += 1;
          }
        }
      }
    }
      
    });

  ////////////////////////////////
  //*** transpose definition ***//
  ////////////////////////////////
  Params transpose_params = 
    {
     {"input_type", CoreIRType::make(c)},
    };

  commonlib->newTypeGen(
    "transpose_type",
    transpose_params,
    [](Context* c, Values genargs) { //Function to compute type
      Type* input_type = genargs.at("input_type")->get<Type*>();
      
      return c->Record({
          {"in",input_type},
          {"out",c->Flip(input_type)}
        });
    }
    );

  Generator* transpose = commonlib->newGeneratorDecl("transpose",
                                                   commonlib->getTypeGen("transpose_type"),
                                                   transpose_params);
  transpose->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    auto input_type = genargs.at("input_type")->get<Type*>();
    auto input_dims = get_dims(input_type);
    input_dims.erase(input_dims.begin());

    // determine number of ports
    int num_ports = 1;
    for (const auto& port_length : input_dims) {
      num_ports *= port_length;
    }

    // store the current port index
    vector<uint> port_idxs(input_dims.size());
    
    for (int idx = 0; idx < num_ports; ++idx) {
      // find the wires associated with the indices
      CoreIR::Wireable* cur_wire = def->sel("self")->sel("in");
      CoreIR::Wireable* opposite_wire = def->sel("self")->sel("out");
      for (size_t i = 0; i < port_idxs.size(); ++i) {
        auto port_idx = port_idxs.at(i);
        auto opposite_idx = input_dims.at(i) - port_idx - 1;
        cur_wire = cur_wire->sel(port_idx);
        opposite_wire = opposite_wire->sel(opposite_idx);
      }

      // connect the wire to transposed version
      def->connect(cur_wire, opposite_wire);
    
      // increment  index
      port_idxs.at(0) += 1;
      for (size_t dim = 0; dim < port_idxs.size(); ++dim) {
        if (port_idxs.at(dim) >= input_dims.at(dim)) {
          port_idxs.at(dim) = 0;
          if (dim + 1 < port_idxs.size()) {
            port_idxs.at(dim+1) += 1;
          }
        }
      }
    }
    });
    
  ////////////////////////////////////////
  //*** transpose reshape definition ***//
  ////////////////////////////////////////

  Generator* transpose_reshape = commonlib->newGeneratorDecl("transpose_reshape",
                                                             commonlib->getTypeGen("reshape_type"),
                                                             reshape_params);
  transpose_reshape->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
      auto input_type = genargs.at("input_type")->get<Type*>();

      auto self = def->sel("self");
      auto transpose = def->addInstance("transpose", "commonlib.transpose", {{"input_type",Const::make(c,input_type)}});
      auto reshape = def->addInstance("reshape", "commonlib.reshape", genargs);
      
      def->connect(self->sel("in"), transpose->sel("in"));
      def->connect(transpose->sel("out"), reshape->sel("in"));
      def->connect(reshape->sel("out"), self->sel("out"));
      
    });


  
  return commonlib;
}


COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(commonlib)
