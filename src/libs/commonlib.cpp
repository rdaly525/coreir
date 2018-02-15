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
  /////////////////////////////////

  //Lazy way:
  unordered_map<string,vector<string>> opmap({
      {"unary",{
        "abs"
    }},
    {"binary",{
      "umin","smin","umax","smax",
      "uclamp","sclamp",
      "absd"
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

  // Define min/max modules

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

  // Define clamp
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

  // Define abs,absd
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
    def->connect("self.in","out_mux.in0");
    def->connect("mult.out","out_mux.in1");

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

  // Define MAD
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

  /////////////////////////////////
  // reg array definition        //
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
      Generator* muxN = commonlib->getGenerator("muxn");

      Const* aWidth = Const::make(c,width);

      if (N == 1) {
        def->connect("self.in.data.0","self.out");
        def->addInstance("term_sel", "corebit.term");
        def->connect("self.in.sel.0", "term_sel.in");
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

        def->connect("muxN_0.out","join.in0");
        def->connect("muxN_1.out","join.in1");

        // wire up selects
        def->connect({"self","in","sel",to_string(Nbits-1)},{"join","sel"});
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
      def->connect("self.in.0","self.out");
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
      def->connect("opN_0.out","join.in0");
      def->connect("opN_1.out","join.in1");
    }

  });

  /////////////////////////////////
  // bitopN definition           //
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
      def->addInstance("join",op2);
      def->connect("join.out","self.out");

      def->connect("self.in.0","join.in0");
      def->connect("self.in.1","join.in1");
    }
    else {
      def->addInstance("join",op2);
      def->connect("join.out","self.out");

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
      def->connect("opN_0.out","join.in0");
      def->connect("opN_1.out","join.in1");
    }

  });


  //Add a LUTN
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




  // generic recursively defined linebuffer
  Params lb_args = 
    {{"input_type",CoreIRType::make(c)},
     {"output_type",CoreIRType::make(c)},
     {"image_type",CoreIRType::make(c)}, 
     {"has_valid",c->Bool()},
     {"is_last_lb",c->Bool()} // use this to denote when to create valid register chain
    };

  commonlib->newTypeGen(
    "lb_type", //name for the typegen
    lb_args,
    [](Context* c, Values genargs) { //Function to compute type
      bool has_valid = genargs.at("has_valid")->get<bool>();
      //bool is_last_lb = genargs.at("is_last_lb")->get<bool>();
      Type* in_type  = genargs.at("input_type")->get<Type*>();
      Type* out_type  = genargs.at("output_type")->get<Type*>();
      RecordParams recordparams = {
          {"in", in_type},
          {"wen",c->BitIn()},
          {"out", out_type}
      };


      if (has_valid) { recordparams.push_back({"valid",c->Bit()}); }
      if (has_valid) { recordparams.push_back({"valid_chain",c->Bit()}); }
      // only register chain needs wen for valid bit propagation
      //if (has_valid && is_last_lb && num_dims(in_type)==2) { recordparams.push_back({"wen",c->BitIn()}); }
      return c->Record(recordparams);
    }
  );

  Generator* lb = commonlib->newGeneratorDecl(
    "linebuffer",
    commonlib->getTypeGen("lb_type"),
    lb_args
  );
  lb->addDefaultGenArgs({{"has_valid",Const::make(c,false)}});
  lb->addDefaultGenArgs({{"is_last_lb",Const::make(c,true)}}); // asserted false to not create register chain

  lb->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    //cout << "running linebuffer generator" << endl;
    bool has_valid = genargs.at("has_valid")->get<bool>();
    bool is_last_lb= genargs.at("is_last_lb")->get<bool>();
    Type* in_type  = genargs.at("input_type")->get<Type*>();
    Type* out_type = genargs.at("output_type")->get<Type*>();
    Type* img_type = genargs.at("image_type")->get<Type*>();
    vector<uint> in_dims = get_dims(in_type);
    vector<uint> out_dims = get_dims(out_type);
    vector<uint> img_dims = get_dims(img_type);

    uint bitwidth = in_dims[0]; // first array is bitwidth
    ASSERT(bitwidth > 0, "The first dimension for the input is interpretted "
					 "as the bitwidth which was set to " + to_string(bitwidth));

    ASSERT(bitwidth == out_dims[0], 
					 to_string(bitwidth) + " != " + to_string(out_dims[0]) + "all bitwidths must match");
    ASSERT(bitwidth == img_dims[0], 
					 to_string(bitwidth) + " != " + to_string(img_dims[0]) + "all bitwidths must match");

    in_dims.erase(in_dims.begin()); // erase the bitwidth size from vectors
    out_dims.erase(out_dims.begin());
    img_dims.erase(img_dims.begin());

    uint num_dims = in_dims.size();
    assert(num_dims >= 0);
    assert(num_dims == out_dims.size()); // all must have same number of dimensions
    assert(num_dims == img_dims.size());

    // we will check just the last dimension
    uint dim = num_dims-1;
    uint out_dim = out_dims[dim];
    uint img_dim = img_dims[dim];
    uint in_dim = in_dims[dim];

    assert(img_dim >= out_dim); // image dimension length must be larger than output
    assert(out_dim >= in_dim); // output stencil size must be larger than the input
    assert(img_dim % in_dim == 0); // dimension length must be divisible, becuase we can't swizzle data
    ASSERT(out_dim % in_dim == 0, "out_dim=" + to_string(out_dim) + " % in_dim=" + to_string(in_dim) + \
           " != 0, dimension length must be divisible, becuase we can't swizzle data");

    // note: only making rowbuffer if more than 1D
    if (img_dim - out_dim < 3 && (img_dim != out_dim) && num_dims > 1) {
      std::cout << "Image dimension " << dim << "  is " << img_dim 
                << " and output stencil size is " << out_dim
                << ", which means the linebuffer mem is going to be very small" << std::endl;
      
    }

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
        uint iflip = (out_dim-1) - i; // output goes to mirror position

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
      if (has_valid && is_last_lb) {
        string valid_prefix = "valreg_";
        for (uint i=0; i<out_dim; i+=in_dim) {
          
          // connect to input wen
          if (i == 0) {
            string reg_name = valid_prefix + to_string(i);
            def->addInstance(reg_name, "corebit.dff");
            def->addInstance("enableConst", "coreir.const", {{"width",aBitwidth}}, {{"value", Const::make(c, 1)}});
            def->connect({"enableConst","out"}, {reg_name,"in"});
         
            // create and connect to register; register connects to previous register
          } else {
            uint in_idx = i - in_dim;
            string reg_name = valid_prefix + to_string(i);
            string prev_reg_name = valid_prefix + to_string(in_idx);
            def->addInstance(reg_name, "corebit.dff");
            def->connect({prev_reg_name, "out"}, {reg_name, "in"});

          }
        }

        // connect last valid bit to self.valid
        string last_valid_name = valid_prefix + to_string(out_dim-in_dim);
        def->connect({"self","valid"},{last_valid_name,"out"});
				def->connect({"self","valid_chain"},{last_valid_name,"out"});
        
      } // valid chain



    //////////////////////////  
    ///// RECURSIVE CASE /////
    //////////////////////////  
    } else {
      //cout << "creating a recursive linebuffer" << endl;
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
            {"is_last_lb", Const::make(c, !has_valid)}
          };
        //if (!has_valid || (is_last_lb && i == out_dim-1)) { // was used when is_last_lb was used recursively
        
        def->addInstance(lb_name, "commonlib.linebuffer", args);

      }

      // ALL CASES: stencil output connections
      // connect the stencil outupts
      for (uint i=0; i<out_dim; ++i) {
        uint iflip = (out_dim-1) - i; // output goes to mirror position
        string lb_name = lb_prefix + to_string(i);
        def->connect({"self","out",to_string(iflip)}, {lb_name,"out"});
      }

      //cout << "created all linebuffers" << endl;
      
      // SPECIAL CASE: same sized stencil output as image, so no lbmems needed (all in regs)
      if (out_dim == img_dim) {
        ASSERT(false, "out_dim == img_dim isn't implemented yet");
        /*
        // connect the inputs
        for (uint i = 0; i < out_dim; ++i) {
          std::string lb_name = lb_prefix + std::to_string(i);
          vector<string> prev_name;

          // lb input depends on how the size of input interface 
          if (i < in_dim) {
            prev_name = {"self", "in", to_string(i)};
          } else {
            prev_name = {lb2_prefix + std::to_string(i-in_dim)), "in"};
          }

          // connect every input for this lb
          for (uint dim_i=0; dim_i<num_dim-1; ++dim) {
            for (uint lb_in; lb_in<in_dims[dim]; ++lb_in) {
              
            }
          }

          def->connect({"self","in"},{lb_name,"in"});
          def->connect(prev_lb,lb_name + "in");
      }
        */

      } else {
        //cout << "in the regular case of linebuffer" << endl;
 
      // REGULAR CASE: lbmems to store image lines
 
      // create lbmems to store data between linebuffers
      //   size_lbmems = prod((img[x] - (out[x]-1)) / in[x]) 
      //      except for x==1, img0 / in0
        uint size_lbmems = out_dim-1;
        for (uint dim_i=0; dim_i<num_dims-1; dim_i++) {
          if (dim_i == 0) {
            size_lbmems *= img_dims[dim_i] / in_dims[dim_i];
          } else {
            size_lbmems *= (img_dims[dim_i] - (out_dims[dim_i]-in_dims[dim_i])) / in_dims[dim_i];
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

            def->addInstance(lbmem_name, "memory.rowbuffer",
                             {{"width",aBitwidth},{"depth",aLbmemSize}});

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

              // connect wen if has_valid
              if (has_valid) {
                 if (out_i < in_dim) {
                   // use self wen; actually stall network for now
                   //def->connect("self.wen", lbmem_name + ".wen");
                   string wen_name = lbmem_name + "_wen_high";
                   Values wen_high = {{"value",Const::make(c,true)}};
                   def->addInstance(wen_name, "corebit.const", wen_high);
                   def->connect({wen_name,"out"}, {lbmem_name,"wen"});
                 } else {
                   // use valid from previous lbmem
                   def->connect(input_name + ".valid", lbmem_name + ".wen");
                 }
              } else {
                string wen_name = lbmem_name + "_wen_high";
                Values wen_high = {{"value",Const::make(c,true)}};
                def->addInstance(wen_name, "corebit.const", wen_high);
                def->connect({wen_name,"out"}, {lbmem_name,"wen"});
              }

            } else {
              ///// connect lbmem inputs for non-2d case /////
              // connect to end of associated linebuffer, which is one of the stencil outputs
              input_name = lb_prefix + to_string(out_i) + ".out";
              for (int dim_i=num_indices-1; dim_i>=0; --dim_i) {
                if (dim_i == 0) {
                  // for last dimension, don't go to the end of register chain
                  input_name += "." + to_string(out_dims[dim_i]-1 - indices[dim_i]);
                } else {
                  input_name += "." + to_string(in_dims[dim_i]-1 - indices[dim_i]);

                }
              }
              def->connect(lbmem_name + ".wdata", input_name);

              // connect wen if has_valid
              if (has_valid) {
                string valid_name = lb_prefix + to_string(0);
                def->connect(valid_name + ".valid_chain", lbmem_name + ".wen");
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
          //if (has_valid) { def->connect({"self","wen"}, {lb_name, "wen"}); } // use stall network
        }

        ///// connect linebuffer outputs /////
        if (has_valid) {
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
          def->connect({"self","valid_chain"},{last_lbmem_name,"valid"});

          // create counters to create valid output (if top-level linebuffer)
          if (is_last_lb) {

            // andr all comparator outputs
            string andr_name = "valid_andr";
            Values andr_params = {{"N",Const::make(c,num_dims-1)},{"operator",Const::make(c,"corebit.and")}};
            def->addInstance(andr_name,"commonlib.bitopn",andr_params);
            def->connect({andr_name,"out"},{"self","valid"});
            
            // create a counter for all but the last dimension
            for (uint dim_i=0; dim_i<num_dims-1; dim_i++) {
              // counter
              string counter_prefix = "valcounter_";
              string counter_name = counter_prefix + to_string(dim_i);
              Values counter_args = {
                {"width",Const::make(c,bitwidth)},
                {"min",Const::make(c,0)},
                {"max",Const::make(c,img_dims[dim_i] / in_dims[dim_i])},
                {"inc",Const::make(c,1)}
              };
              def->addInstance(counter_name,"commonlib.counter",counter_args);

              // comparator for valid (if stencil_size < count)
              string compare_name = "valcompare_" + to_string(dim_i);
              def->addInstance(compare_name,"coreir.ult",{{"width",aBitwidth}});
              string const_name = "const_stencil" + to_string(dim_i);
              Values const_value = {{"value",Const::make(c,BitVector(bitwidth,out_dims[dim_i] / in_dims[dim_i]))}};
              def->addInstance(const_name, "coreir.const", {{"width",aBitwidth}}, const_value);


              // connections
              // counter en by valid or overflow bit
              if (dim_i == 0) {
                def->connect({last_lbmem_name,"valid"},{counter_name,"en"});
              } else {
                string last_counter_name = counter_prefix + to_string(dim_i-1);
                def->connect({last_counter_name,"overflow"},{counter_name,"en"});
              }

              // wire up comparator
              def->connect({const_name,"out"},{compare_name,"in0"});
              def->connect({counter_name,"out"},{compare_name,"in1"});
              def->connect({compare_name,"out"},{andr_name,"in",to_string(dim_i)});
            }
          }

          /*
          // connect last linebuffer output to self.valid
          string last_lb_name = lb_prefix + to_string(out_dim-1);
          def->connect({"self","valid"},{last_lb_name,"valid"});
          if (num_dims==2 && is_last_lb) {
            def->connect({last_lb_name,"wen"},{last_lbmem_name,"valid"});
            }*/

        }
        
        
      } // regular case

    }
    });


  /*
   * DEPRECATED: DO NOT USE 2D or 3D IMPLEMENTATION, LINEBUFFER HANLDES MULTIPLE DIMENSIONS
   */
  //Linebuffer2d
  //Declare a TypeGenerator (in global) for 2d linebuffer
  commonlib->newTypeGen(
    "linebuffer2d_type", //name for the typegen
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

  Generator* linebuffer2d = commonlib->newGeneratorDecl(
    "linebuffer2d",
    commonlib->getTypeGen("linebuffer2d_type"),{
      {"stencil_width",c->Int()},
      {"stencil_height",c->Int()},
      {"image_width",c->Int()},
      {"bitwidth",c->Int()}
    }
  );
  linebuffer2d->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint stencil_width  = genargs.at("stencil_width")->get<int>();
    uint stencil_height  = genargs.at("stencil_height")->get<int>();
    uint image_width = genargs.at("image_width")->get<int>();
    uint bitwidth = genargs.at("bitwidth")->get<int>();
    isPowerOfTwo(bitwidth);
    assert(stencil_height > 0);
    assert(stencil_width > 0);
    assert(image_width >= stencil_width);
    assert(bitwidth > 0);

    if (image_width - stencil_width < 3 && (image_width != stencil_width)) {
      std::cout << "Image width is " << image_width << " and stencil width " << stencil_width
                << ", which means the 2d linebuffer is going to be very small" << std::endl;
    }

    Const* aBitwidth = Const::make(c,bitwidth);
    assert(isa<ConstInt>(aBitwidth));
    Const* aImageWidth = Const::make(c,image_width);
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
        def->addInstance(mem_name,"memory.rowbuffer",{{"width",aBitwidth},{"depth",aImageWidth}});
        def->addInstance(mem_name+"_valid_term","corebit.term");
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

    // ALL CASES: all dimensions
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
    "linebuffer3d_type", //name for the typegen
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

  /*
   * DEPRECATED: DO NOT USE 2D or 3D IMPLEMENTATION, LINEBUFFER HANLDES MULTIPLE DIMENSIONS
   */
  Generator* linebuffer3d = commonlib->newGeneratorDecl(
    "linebuffer3d",
    commonlib->getTypeGen("linebuffer3d_type"),{
      {"stencil_d0",c->Int()},
      {"stencil_d1",c->Int()},
      {"stencil_d2",c->Int()},
      {"image_d0",c->Int()},
      {"image_d1",c->Int()},
      {"bitwidth",c->Int()}
    }
  );
  linebuffer3d->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint stencil_d0  = args.at("stencil_d0")->get<int>();
    uint stencil_d1  = args.at("stencil_d1")->get<int>();
    uint stencil_d2  = args.at("stencil_d2")->get<int>();
    uint image_d0 = args.at("image_d0")->get<int>();
    uint image_d1 = args.at("image_d1")->get<int>();
    uint bitwidth = args.at("bitwidth")->get<int>();
    isPowerOfTwo(bitwidth);
    assert(stencil_d0 > 0);
    assert(stencil_d1 > 0);
    assert(stencil_d2 > 0);
    assert(image_d0 >= stencil_d0);
    assert(image_d1 >= stencil_d1);
    assert(bitwidth > 0);

    Const* aBitwidth = Const::make(c,bitwidth);

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
      def->addInstance(lb2_name, "commonlib.linebuffer2d", args);
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
        def->addInstance(mem_name,"memory.rowbuffer",{{"width",aBitwidth},{"depth",aLBWidth}});
        def->addInstance(mem_name+"_valid_term", "corebit.term");
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
        {"out",c->Bit()->Arr(width)},
        {"overflow",c->Bit()}
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
    //def->addInstance("and", "corebit.and");

    // wire up modules
    // clear if max < count+inc
    def->connect("count.out","self.out");
    def->connect("count.out","add.in0");
    def->connect("inc.out","add.in1");

    def->connect("self.en","count.en");
    def->connect("add.out","count.in");

    def->connect("add.out","ult.in1");
    def->connect("max.out","ult.in0");
    def->connect("ult.out","count.clr");
    def->connect("ult.out","self.overflow");

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
    assert(width > num_bits(rate-1)); // not enough bits in counter for rate

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
    Values sliceArgs = {{"width", Const::make(c,width)},
                        {"lo", Const::make(c,0)},
                        {"hi", Const::make(c,num_bits(rate-1))}};
    def->addInstance("slice", "coreir.slice", sliceArgs);
    
    // all but input0 are stored in registers
    for (uint i=1; i<rate; ++i) {
      std::string reg_name = "reg_" + std::to_string(i);
      def->addInstance(reg_name, "mantle.reg",
                       {{"width",aBitwidth},{"has_en",Const::make(c,true)}});
    }

    // wire up modules
    def->connect("self.en","counter.en");
    def->connect("counter.out","self.count");

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
  // decoder definition          //
  /////////////////////////////////

  // on count==0, read in all input values.
  // on every cycle, input<n> is outputted where n=count

  // Not yet implemented

  return commonlib;
}


COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(commonlib)
