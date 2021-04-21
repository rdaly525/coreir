#include "coreir/libs/commonlib.h"
#include "coreir/libs/aetherlinglib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(commonlib);

using namespace std;
using namespace CoreIR;

uint num_bits(uint N) {
  if (N == 0) { return 1; }

  uint num_shifts = 0;
  uint temp_value = N;
  while (temp_value > 0) {
    temp_value = temp_value >> 1;
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
  while (!cType->isBaseType()) {
    if (auto aType = dyn_cast<ArrayType>(cType)) {

      uint length = aType->getLen();

      cType = aType->getElemType();
      if (cType->isBaseType()) { bitwidth = length; }
      else {
        lengths.insert(lengths.begin(), length);
        // lengths.push_back(length);
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
  while (!cType->isBaseType()) {
    assert(cType->getKind() == Type::TypeKind::TK_Array);
    ArrayType* aType = static_cast<ArrayType*>(cType);
    cType = aType->getElemType();

    num_dims++;
  }
  return num_dims;
}

bool isPowerOfTwo(const uint n) {
  if (n == 0) { return 0; }

  return (n & (n - 1)) == 0;
}

uint inverted_index(uint outx, uint inx, uint i) {
  return (outx - 1) - (inx - 1 - i % inx) - (i / inx) * inx;
}

vector<CoreIR::Wireable*> get_wires(
  CoreIR::Wireable* base_wire,
  const vector<size_t> ports) {
  int num_ports = 1;
  for (const auto& port_length : ports) { num_ports *= port_length; }

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
        if (dim + 1 < port_idxs.size()) { port_idxs.at(dim + 1) += 1; }
      }
    }
  }

  return all_wires;
}

void connect_wires(
  ModuleDef* def,
  vector<Wireable*> in_wires,
  vector<Wireable*> out_wires) {
  assert(in_wires.size() == out_wires.size());

  for (size_t idx = 0; idx < in_wires.size(); ++idx) {
    def->connect(in_wires.at(idx), out_wires.at(idx));
  }
}

Namespace* CoreIRLoadLibrary_commonlib(Context* c) {

  Namespace* commonlib = c->newNamespace("commonlib");
  Namespace* coreirprims = c->getNamespace("coreir");

  /////////////////////////////////
  // Commonlib Types
  /////////////////////////////////

  Params widthparams = Params({{"width", c->Int()}});
  // TypeGens defined in coreirprims

  // For MAD
  coreirprims->newTypeGen("ternary", widthparams, [](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
    Type* ptype = c->Bit()->Arr(width);
    return c->Record({{"in0", c->Flip(ptype)},
                      {"in1", c->Flip(ptype)},
                      {"in2", c->Flip(ptype)},
                      {"out", ptype}});
  });

  // muxN type
  commonlib->newTypeGen(
    "muxN_type",                             // name for the typegen
    {{"width", c->Int()}, {"N", c->Int()}},  // generater parameters
    [](Context* c, Values genargs) {         // Function to compute type
      uint width = genargs.at("width")->get<int>();
      uint N = genargs.at("N")->get<int>();
      return c->Record(
        {{"in",
          c->Record({{"data", c->BitIn()->Arr(width)->Arr(N)},
                     {"sel", c->BitIn()->Arr(num_bits(N - 1))}})},
         {"out", c->Bit()->Arr(width)}});
    });

  // opN type
  commonlib->newTypeGen(
    "opN_type",  // name for the typegen
    {{"width", c->Int()},
     {"N", c->Int()},
     {"operator", c->String()}},      // generater parameters
    [](Context* c, Values genargs) {  // Function to compute type
      uint width = genargs.at("width")->get<int>();
      uint N = genargs.at("N")->get<int>();
      return c->Record({{"in", c->BitIn()->Arr(width)->Arr(N)},
                        {"out", c->Bit()->Arr(width)}});
    });

  // bitopN type
  commonlib->newTypeGen(
    "bitopN_type",                                 // name for the typegen
    {{"N", c->Int()}, {"operator", c->String()}},  // generater parameters
    [](Context* c, Values genargs) {               // Function to compute type
      uint N = genargs.at("N")->get<int>();
      return c->Record({{"in", c->BitIn()->Arr(N)}, {"out", c->Bit()}});
    });

  /////////////////////////////////
  // Commonlib Arithmetic primitives
  //   umin,smin,umax,smax
  //   uclamp, sclamp
  //   abs, absd, MAD
  //   div
  /////////////////////////////////

  // Lazy way:
  unordered_map<string, vector<string>> opmap({
    {"unary", {"abs"}},
    {"binary",
     {
       "umin",
       "smin",
       "umax",
       "smax",
       "uclamp",
       "sclamp",
       "absd",
       "div",
       "mult_middle",
       "mult_high",
     }},
    {"ternary", {"MAD"}},
  });

  // Add all the generators (with widthparams)
  for (auto tmap : opmap) {
    TypeGen* tg = coreirprims->getTypeGen(tmap.first);
    for (auto op : tmap.second) {
      commonlib->newGeneratorDecl(op, tg, widthparams);
    }
  }

  //*** Define min/max modules ***//

  Generator* umin = c->getGenerator("commonlib.umin");
  umin->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width == 16, "NYI non 16");
    def->addInstance("ucomp", "coreir.ule", args);
    def->addInstance("min_mux", "coreir.mux", args);
    def->connect("self.in0", "ucomp.in0");
    def->connect("self.in1", "ucomp.in1");
    def->connect("ucomp.out", "min_mux.sel");
    def->connect("self.in1", "min_mux.in0");
    def->connect("self.in0", "min_mux.in1");
    def->connect("self.out", "min_mux.out");
  });

  Generator* smin = c->getGenerator("commonlib.smin");
  smin->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width == 16, "NYI non 16");
    def->addInstance("scomp", "coreir.sle", args);
    def->addInstance("min_mux", "coreir.mux", args);
    def->connect("self.in0", "scomp.in0");
    def->connect("self.in1", "scomp.in1");
    def->connect("scomp.out", "min_mux.sel");
    def->connect("self.in1", "min_mux.in0");
    def->connect("self.in0", "min_mux.in1");
    def->connect("self.out", "min_mux.out");
  });

  Generator* umax = c->getGenerator("commonlib.umax");
  umax->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width == 16, "NYI non 16");
    def->addInstance("ucomp", "coreir.uge", args);
    def->addInstance("max_mux", "coreir.mux", args);
    def->connect("self.in0", "ucomp.in0");
    def->connect("self.in1", "ucomp.in1");
    def->connect("ucomp.out", "max_mux.sel");
    def->connect("self.in1", "max_mux.in0");
    def->connect("self.in0", "max_mux.in1");
    def->connect("self.out", "max_mux.out");
  });

  Generator* smax = c->getGenerator("commonlib.smax");
  smax->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    ASSERT(width == 16, "NYI non 16");
    def->addInstance("scomp", "coreir.sge", args);
    def->addInstance("max_mux", "coreir.mux", args);
    def->connect("self.in0", "scomp.in0");
    def->connect("self.in1", "scomp.in1");
    def->connect("scomp.out", "max_mux.sel");
    def->connect("self.in1", "max_mux.in0");
    def->connect("self.in0", "max_mux.in1");
    def->connect("self.out", "max_mux.out");
  });

  //*** Define clamp ***//
  Generator* uclamp = c->getGenerator("commonlib.uclamp");
  uclamp->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("max", "coreir.umax", args);
    def->addInstance("min", "coreir.umin", args);
    def->connect("self.in0", "max.in0");
    def->connect("self.in1", "max.in1");
    def->connect("self.in2", "min.in0");
    def->connect("max.out", "min.in1");
    def->connect("self.out", "min.out");
  });

  Generator* sclamp = c->getGenerator("commonlib.sclamp");
  sclamp->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("max", "coreir.smax", args);
    def->addInstance("min", "coreir.smin", args);
    def->connect("self.in0", "max.in0");
    def->connect("self.in1", "max.in1");
    def->connect("self.in2", "min.in0");
    def->connect("max.out", "min.in1");
    def->connect("self.out", "min.out");
  });

  //*** Define abs,absd ***//
  Generator* abs = c->getGenerator("commonlib.abs");
  abs->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    def->addInstance("out_mux", "coreir.mux", args);
    def->addInstance("is_pos", "coreir.sge", args);
    def->addInstance("mult", "coreir.mul", args);

    def->addInstance(
      "negone_const",
      "coreir.const",
      {{"width", Const::make(c, width)}},
      {{"value", Const::make(c, width, -1)}});
    def->addInstance(
      "zero_const",
      "coreir.const",
      {{"width", Const::make(c, width)}},
      {{"value", Const::make(c, width, 0)}});

    // is_pos = in > 0
    def->connect("self.in", "is_pos.in0");
    def->connect("zero_const.out", "is_pos.in1");

    // in * -1
    def->connect("negone_const.out", "mult.in0");
    def->connect("self.in", "mult.in1");

    // is_pos ? in : -in
    def->connect("is_pos.out", "out_mux.sel");
    def->connect("self.in", "out_mux.in1");
    def->connect("mult.out", "out_mux.in0");

    def->connect("out_mux.out", "self.out");
  });

  Generator* absd = c->getGenerator("commonlib.absd");
  absd->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("abs", "commonlib.abs", args);
    def->addInstance("sub", "coreir.sub", args);

    def->connect("self.in0", "sub.in0");
    def->connect("self.in1", "sub.in1");
    def->connect("sub.out", "abs.in");
    def->connect("abs.out", "self.out");
  });

  //*** Define iterative divider ***//
  // Generator* div = c->getGenerator("commonlib.div");
  // TODO: implement divider

  //*** Define MAD ***//
  Generator* MAD = c->getGenerator("commonlib.MAD");
  MAD->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    def->addInstance("mult", "coreir.mul", args);
    def->addInstance("add", "coreir.add", args);

    def->connect("self.in0", "mult.in0");
    def->connect("self.in1", "mult.in1");
    def->connect("self.in2", "add.in0");
    def->connect("mult.out", "add.in1");
    def->connect("add.out", "self.out");
  });


  //*** Define multiplier variations ***//
  Generator* mult_middle = c->getGenerator("commonlib.mult_middle");
  mult_middle->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      uint width = args.at("width")->get<int>();
      Values sextArgs = {{"width_in", Const::make(c, width)},
                          {"width_out", Const::make(c, 2*width)}};
      def->addInstance("sexta", "coreir.sext", sextArgs);
      def->addInstance("sextb", "coreir.sext", sextArgs);

      def->addInstance("mult", "coreir.mul", {{"width", Const::make(c, 2*width)}});
      
      Values sliceArgs = {{"width", Const::make(c, 2*width)},
                          {"lo", Const::make(c, width/2)},
                          {"hi", Const::make(c, 3*width/2)}};
      def->addInstance("slice", "coreir.slice", sliceArgs);

      def->connect("self.in0", "sexta.in");
      def->connect("self.in1", "sextb.in");
      def->connect("sexta.out", "mult.in0");
      def->connect("sextb.out", "mult.in1");
      def->connect("mult.out", "slice.in");
      def->connect("slice.out", "self.out");
  });

  Generator* mult_high = c->getGenerator("commonlib.mult_high");
  mult_high->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
      uint width = args.at("width")->get<int>();
      Values sextArgs = {{"width_in", Const::make(c, width)},
                          {"width_out", Const::make(c, 2*width)}};
      def->addInstance("sexta", "coreir.sext", sextArgs);
      def->addInstance("sextb", "coreir.sext", sextArgs);

      def->addInstance("mult", "coreir.mul", {{"width", Const::make(c, 2*width)}});
      
      Values sliceArgs = {{"width", Const::make(c, 2*width)},
                          {"lo", Const::make(c, width)},
                          {"hi", Const::make(c, 2*width)}};
      def->addInstance("slice", "coreir.slice", sliceArgs);

      def->connect("self.in0", "sexta.in");
      def->connect("self.in1", "sextb.in");
      def->connect("sexta.out", "mult.in0");
      def->connect("sextb.out", "mult.in1");
      def->connect("mult.out", "slice.in");
      def->connect("slice.out", "self.out");
  });

  //*** Define demux2 ***//
  // TODO: implement demux

  ///////////////////////////////////
  //*** const array definition  ***//
  ///////////////////////////////////

  Params const_array_args = {{"type", CoreIRType::make(c)},
                             {"value", c->Int()}};
  TypeGen* constArrayTG = coreirprims->newTypeGen(
    "constArrayTG",
    const_array_args,
    [](Context* c, Values args) {
      Type* t = args.at("type")->get<Type*>();

      RecordParams r({{"out", t}});
      return c->Record(r);
    });
  Generator* const_array = commonlib->newGeneratorDecl(
    "const_array",
    constArrayTG,
    const_array_args);
  const_array->addDefaultGenArgs({{"value", Const::make(c, 0)}});

  const_array->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      Type* type = args.at("type")->get<Type*>();
      int value = args.at("value")->get<int>();
      Type* cType = type;

      // identify type size
      vector<uint> lengths;
      uint bitwidth = 1;
      while (!cType->isBaseType()) {
        assert(cType->getKind() == Type::TypeKind::TK_Array);
        ArrayType* aType = static_cast<ArrayType*>(cType);
        uint length = aType->getLen();

        cType = aType->getElemType();
        if (cType->isBaseType()) { bitwidth = length; }
        else {
          // lengths.insert(lengths.begin(), length);
          lengths.push_back(length);
        }
      }

      // create and connect the interface
      Wireable* pt_out = def->addInstance(
        "pt_out",
        "mantle.wire",
        {{"type", Const::make(c, type)}});
      def->connect("self.out", "pt_out.out");

      // collect all interface wires
      std::vector<Wireable*> out_wires;
      out_wires.push_back(pt_out->sel("in"));
      for (uint dim_length : lengths) {
        std::vector<Wireable*> out_temp;
        out_temp.reserve(out_wires.size() * dim_length);

        for (uint i = 0; i < dim_length; ++i) {
          for (auto out_wire : out_wires) {
            out_temp.push_back(out_wire->sel(i));
          }
        }
        out_wires = out_temp;
      }

      // create and wire up constants
      for (uint i = 0; i < out_wires.size(); ++i) {
        std::string const_name = "const_" + std::to_string(i);
        Values const_args = {{"width", Const::make(c, bitwidth)}};

        Values const_configargs = {
          {"value", Const::make(c, BitVector(bitwidth, value))}};
        Wireable* const_inst = def->addInstance(
          const_name,
          "coreir.const",
          const_args,
          const_configargs);
        def->connect(const_inst->sel("out"), out_wires[i]);
      }
    });

  /////////////////////////////////
  //*** reg array definition  ***//
  /////////////////////////////////

  Params reg_array_args = {{"type", CoreIRType::make(c)},
                           {"has_en", c->Bool()},
                           {"has_clr", c->Bool()},
                           {"has_rst", c->Bool()},
                           {"init", c->Int()}};
  TypeGen* regArrayTG = coreirprims->newTypeGen(
    "regArrayTG",
    reg_array_args,
    [](Context* c, Values args) {
      Type* t = args.at("type")->get<Type*>();
      bool en = args.at("has_en")->get<bool>();
      bool clr = args.at("has_clr")->get<bool>();
      bool rst = args.at("has_rst")->get<bool>();
      assert(!(clr && rst));

      RecordParams r({{"in", t->getFlipped()},
                      {"clk", c->Named("coreir.clkIn")},
                      {"out", t}});
      if (en) r.push_back({"en", c->BitIn()});
      if (clr) r.push_back({"clr", c->BitIn()});
      if (rst) r.push_back({"rst", c->BitIn()});
      return c->Record(r);
    });
  Generator* reg_array = commonlib->newGeneratorDecl(
    "reg_array",
    regArrayTG,
    reg_array_args);
  reg_array->addDefaultGenArgs({{"has_en", Const::make(c, false)},
                                {"has_clr", Const::make(c, false)},
                                {"has_rst", Const::make(c, false)},
                                {"init", Const::make(c, 0)}});

  reg_array->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      Type* type = args.at("type")->get<Type*>();
      bool en = args.at("has_en")->get<bool>();
      bool clr = args.at("has_clr")->get<bool>();
      bool rst = args.at("has_rst")->get<bool>();
      int init = args.at("init")->get<int>();
      Type* cType = type;

      // identify type size
      vector<uint> lengths;
      uint bitwidth = 1;
      while (!cType->isBaseType()) {
        assert(cType->getKind() == Type::TypeKind::TK_Array);
        ArrayType* aType = static_cast<ArrayType*>(cType);
        uint length = aType->getLen();

        cType = aType->getElemType();
        if (cType->isBaseType()) { bitwidth = length; }
        else {
          // lengths.insert(lengths.begin(), length);
          lengths.push_back(length);
        }
      }

      // create and connect the interface
      Wireable* pt_in = def->addInstance(
        "pt_in",
        "mantle.wire",
        {{"type", Const::make(c, type)}});
      Wireable* pt_out = def->addInstance(
        "pt_out",
        "mantle.wire",
        {{"type", Const::make(c, type)}});
      def->connect("self.in", "pt_in.in");
      def->connect("self.out", "pt_out.out");

      // collect all interface wires
      std::vector<Wireable*> in_wires;
      in_wires.push_back(pt_in->sel("out"));
      std::vector<Wireable*> out_wires;
      out_wires.push_back(pt_out->sel("in"));
      for (uint dim_length : lengths) {
        std::vector<Wireable*> in_temp;
        std::vector<Wireable*> out_temp;
        in_temp.reserve(in_wires.size() * dim_length);
        out_temp.reserve(out_wires.size() * dim_length);

        for (uint i = 0; i < dim_length; ++i) {
          for (auto in_wire : in_wires) { in_temp.push_back(in_wire->sel(i)); }
          for (auto out_wire : out_wires) {
            out_temp.push_back(out_wire->sel(i));
          }
        }
        in_wires = in_temp;
        out_wires = out_temp;
      }

      // create and wire up registers
      assert(in_wires.size() == out_wires.size());
      for (uint i = 0; i < in_wires.size(); ++i) {
        std::string reg_name = "reg_" + std::to_string(i);
        Values reg_args = {{"width", Const::make(c, bitwidth)},
                           {"has_en", Const::make(c, en)},
                           {"has_clr", Const::make(c, clr)},
                           {"has_rst", Const::make(c, rst)}};
        Values reg_configargs = {
          {"init", Const::make(c, BitVector(bitwidth, init))}};
        Wireable* reg = def->addInstance(
          reg_name,
          "mantle.reg",
          reg_args,
          reg_configargs);
        if (en) { def->connect("self.en", reg_name + ".en"); }
        if (clr) { def->connect("self.clr", reg_name + ".clr"); }
        if (rst) { def->connect("self.rst", reg_name + ".rst"); }
        def->connect(in_wires[i], reg->sel("in"));
        def->connect(reg->sel("out"), out_wires[i]);
      }
    });

  /////////////////////////////////
  //*** muxN definition       ***//
  /////////////////////////////////

  Generator* muxN = commonlib->newGeneratorDecl(
    "muxn",
    commonlib->getTypeGen("muxN_type"),
    {{"width", c->Int()}, {"N", c->Int()}});

  muxN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint N = genargs.at("N")->get<int>();
    assert(N > 0);
    Namespace* stdlib = c->getNamespace("coreir");
    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* mux2 = stdlib->getGenerator("mux");
    Generator* muxN = commonlib->getGenerator("muxn");

    Const* aWidth = Const::make(c, width);

    if (N == 1) {
      def->connect("self.in.data.0", "self.out");
      def->addInstance("term_sel", "corebit.term");
      def->connect("self.in.sel.0", "term_sel.in");
    }
    else if (N == 2) {
      def->addInstance("_join", mux2, {{"width", aWidth}});
      def->connect("_join.out", "self.out");

      def->connect("self.in.data.0", "_join.in0");
      def->connect("self.in.data.1", "_join.in1");
      def->connect("self.in.sel.0", "_join.sel");
    }
    else {
      def->addInstance("_join", mux2, {{"width", aWidth}});
      def->connect("_join.out", "self.out");

      // Connect half instances
      uint Nbits = num_bits(N - 1);  // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits - 1);
      uint Nsmallhalf = N - Nlargehalf;

      // cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking
      // into " << Nlargehalf << " and " << Nsmallhalf <<endl;

      Const* aNlarge = Const::make(c, Nlargehalf);
      Const* aNsmall = Const::make(c, Nsmallhalf);

      def->addInstance("muxN_0", muxN, {{"width", aWidth}, {"N", aNlarge}});
      def->addInstance("muxN_1", muxN, {{"width", aWidth}, {"N", aNsmall}});

      for (uint i = 0; i < Nlargehalf; ++i) {
        def->connect(
          {"self", "in", "data", to_string(i)},
          {"muxN_0", "in", "data", to_string(i)});
      }

      for (uint i = 0; i < Nsmallhalf; ++i) {
        def->connect(
          {"self", "in", "data", to_string(i + Nlargehalf)},
          {"muxN_1", "in", "data", to_string(i)});
      }

      def->connect("muxN_0.out", "_join.in0");
      def->connect("muxN_1.out", "_join.in1");

      // wire up selects
      def->connect(
        {"self", "in", "sel", to_string(Nbits - 1)},
        {"_join", "sel"});
      Values sliceArgs0 = {{"width", Const::make(c, Nbits)},
                           {"lo", Const::make(c, 0)},
                           {"hi", Const::make(c, num_bits(Nlargehalf - 1))}};
      Values sliceArgs1 = {{"width", Const::make(c, Nbits)},
                           {"lo", Const::make(c, 0)},
                           {"hi", Const::make(c, num_bits(Nsmallhalf - 1))}};

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

  Generator* opN = commonlib->newGeneratorDecl(
    "opn",
    commonlib->getTypeGen("opN_type"),
    {{"width", c->Int()}, {"N", c->Int()}, {"operator", c->String()}});

  opN->setGeneratorDefFromFun([](Context* c, Values genargs, ModuleDef* def) {
    uint width = genargs.at("width")->get<int>();
    uint N = genargs.at("N")->get<int>();
    std::string op2 = genargs.at("operator")->get<string>();
    assert(N > 0);

    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* opN = commonlib->getGenerator("opn");

    Const* aWidth = Const::make(c, width);
    Const* aOperator = Const::make(c, op2);

    if (N == 1) { def->connect("self.in.0", "self.out"); }
    else if (N == 2) {
      def->addInstance("_join", op2, {{"width", aWidth}});
      def->connect("_join.out", "self.out");

      def->connect("self.in.0", "_join.in0");
      def->connect("self.in.1", "_join.in1");
    }
    else {
      def->addInstance("_join", op2, {{"width", aWidth}});
      def->connect("_join.out", "self.out");

      // Connect half instances
      uint Nbits = num_bits(N - 1);  // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits - 1);
      uint Nsmallhalf = N - Nlargehalf;

      // cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking
      // into " << Nlargehalf << " and " << Nsmallhalf <<endl;
      Const* aNlarge = Const::make(c, Nlargehalf);
      Const* aNsmall = Const::make(c, Nsmallhalf);

      def->addInstance(
        "opN_0",
        opN,
        {{"width", aWidth}, {"N", aNlarge}, {"operator", aOperator}});
      def->addInstance(
        "opN_1",
        opN,
        {{"width", aWidth}, {"N", aNsmall}, {"operator", aOperator}});
      for (uint i = 0; i < Nlargehalf; ++i) {
        def->connect(
          {"self", "in", to_string(i)},
          {"opN_0", "in", to_string(i)});
      }
      for (uint i = 0; i < Nsmallhalf; ++i) {
        def->connect(
          {"self", "in", to_string(i + Nlargehalf)},
          {"opN_1", "in", to_string(i)});
      }
      def->connect("opN_0.out", "_join.in0");
      def->connect("opN_1.out", "_join.in1");
    }
  });

  /////////////////////////////////
  //*** bitopN definition     ***//
  /////////////////////////////////

  Generator* bitopN = commonlib->newGeneratorDecl(
    "bitopn",
    commonlib->getTypeGen("bitopN_type"),
    {{"N", c->Int()}, {"operator", c->String()}});

  bitopN->setGeneratorDefFromFun([](
                                   Context* c,
                                   Values genargs,
                                   ModuleDef* def) {
    uint N = genargs.at("N")->get<int>();
    std::string op2 = genargs.at("operator")->get<string>();
    assert(N > 0);

    Namespace* commonlib = c->getNamespace("commonlib");
    Generator* opN = commonlib->getGenerator("bitopn");

    Const* aOperator = Const::make(c, op2);

    if (N == 1) { def->connect("self.in.0", "self.out"); }
    else if (N == 2) {
      def->addInstance("_join", op2);
      def->connect("_join.out", "self.out");

      def->connect("self.in.0", "_join.in0");
      def->connect("self.in.1", "_join.in1");
    }
    else {
      def->addInstance("_join", op2);
      def->connect("_join.out", "self.out");

      // Connect half instances
      uint Nbits = num_bits(N - 1);  // 4 inputs has a max index of 3
      uint Nlargehalf = 1 << (Nbits - 1);
      uint Nsmallhalf = N - Nlargehalf;

      // cout << "N=" << N << " which has bitwidth " << Nbits << ", breaking
      // into " << Nlargehalf << " and " << Nsmallhalf <<endl;
      Const* aNlarge = Const::make(c, Nlargehalf);
      Const* aNsmall = Const::make(c, Nsmallhalf);

      def->addInstance("opN_0", opN, {{"N", aNlarge}, {"operator", aOperator}});
      def->addInstance("opN_1", opN, {{"N", aNsmall}, {"operator", aOperator}});
      for (uint i = 0; i < Nlargehalf; ++i) {
        def->connect(
          {"self", "in", to_string(i)},
          {"opN_0", "in", to_string(i)});
      }
      for (uint i = 0; i < Nsmallhalf; ++i) {
        def->connect(
          {"self", "in", to_string(i + Nlargehalf)},
          {"opN_1", "in", to_string(i)});
      }
      def->connect("opN_0.out", "_join.in0");
      def->connect("opN_1.out", "_join.in1");
    }
  });

  //*** Add a LUTN ***//
  auto LUTModParamFun =
    [](Context* c, Values genargs) -> std::pair<Params, Values> {
    Params p;  // params
    Values d;  // defaults
    int N = genargs.at("N")->get<int>();
    p["init"] = c->BitVector(1 << N);
    return {p, d};
  };

  Params lutNParams({{"N", c->Int()}});
  commonlib->newTypeGen("lutNType", lutNParams, [](Context* c, Values genargs) {
    uint N = genargs.at("N")->get<int>();
    return c->Record({{"in", c->BitIn()->Arr(N)}, {"out", c->Bit()}});
  });
  Generator* lutN = commonlib->newGeneratorDecl(
    "lutN",
    commonlib->getTypeGen("lutNType"),
    lutNParams);
  lutN->setModParamsGen(LUTModParamFun);

  // TODO this really should exist in a separate verilog definitions file for
  // commonlib Set verilog for the LutN
  json vjson;
  vjson["parameters"] = {"init"};
  vjson["interface"] = {"input [N-1:0] in", "output out"};
  vjson["definition"] = "  assign out = init[in];";
  lutN->getMetaData()["verilog"] = vjson;

  /////////////////////////////////
  //*** counter definition    ***//
  /////////////////////////////////

  // counter follows a for loop of format:
  //   for ( int i = $min ; $min <= $max ; i += $inc )
  // input:  "valid", when to start counting
  // output: "i", the count

  // counter type
  commonlib->newTypeGen(
    "counter_type",  // name for the typegen
    {{"width", c->Int()},
     {"min", c->Int()},
     {"max", c->Int()},
     {"inc", c->Int()}},              // generater parameters
    [](Context* c, Values genargs) {  // Function to compute type
      uint width = genargs.at("width")->get<int>();
      return c->Record({{"en", c->BitIn()},
                        {"reset", c->BitIn()},
                        {"out", c->Bit()->Arr(width)},
                        {"overflow", c->Bit()}});
    });

  // commonlib->newGeneratorDecl("counter",commonlib->getTypeGen("counter_type"),{{"width",c->Int()},{"min",c->Int()},{"max",c->Int()},{"inc",c->Int()}});
  Generator* counter = commonlib->newGeneratorDecl(
    "counter",
    commonlib->getTypeGen("counter_type"),
    {{"width", c->Int()},
     {"min", c->Int()},
     {"max", c->Int()},
     {"inc", c->Int()}});
  counter->setGeneratorDefFromFun(
    [](Context* c, Values genargs, ModuleDef* def) {
      uint width = genargs.at("width")->get<int>();
      uint max = genargs.at("max")->get<int>();
      uint min = genargs.at("min")->get<int>();
      uint inc = genargs.at("inc")->get<int>();
      assert(width > 0);
      if (max == min) {
        def->addInstance(
          "count_const",
          "coreir.const",
          {{"width", Const::make(c, width)}},
          {{"value", Const::make(c, width, max)}});
        def->addInstance(
          "one_const",
          "corebit.const",
          {{"value", Const::make(c, true)}});

        def->connect("self.out", "count_const.out");
        def->connect("self.overflow", "one_const.out");
      }
      else {

        ASSERT(
          max > min,
          "max is " + to_string(max) + " while min is " + to_string(min));

        // get generators
        Namespace* coreirprims = c->getNamespace("coreir");
        Generator* ult_gen = coreirprims->getGenerator("ult");
        Generator* add_gen = coreirprims->getGenerator("add");
        Generator* const_gen = coreirprims->getGenerator("const");

        // create hardware
        Const* aBitwidth = Const::make(c, width);
        Const* aReset = Const::make(c, BitVector(width, min));
        def->addInstance(
          "count",
          "mantle.reg",
          {{"width", aBitwidth},
           {"has_clr", Const::make(c, true)},
           {"has_en", Const::make(c, true)}},
          {{"init", aReset}});

        def->addInstance(
          "max",
          const_gen,
          {{"width", aBitwidth}},
          {{"value", Const::make(c, BitVector(width, max))}});
        def->addInstance(
          "inc",
          const_gen,
          {{"width", aBitwidth}},
          {{"value", Const::make(c, BitVector(width, inc))}});
        def->addInstance("ult", ult_gen, {{"width", aBitwidth}});
        def->addInstance("add", add_gen, {{"width", aBitwidth}});
        def->addInstance("and", "corebit.and");
        def->addInstance("resetOr", "corebit.or");

        // wire up modules
        // clear if max < count+inc && en == 1
        def->connect("count.out", "self.out");
        def->connect("count.out", "add.in0");
        def->connect("inc.out", "add.in1");

        def->connect("self.en", "count.en");
        def->connect("add.out", "count.in");

        def->connect("add.out", "ult.in1");
        def->connect("max.out", "ult.in0");

        def->connect("ult.out", "and.in0");
        def->connect("self.en", "and.in1");
        // and.out === (max < count+inc  &&  en == 1)

        // clear count on either getting to max or reset
        def->connect("and.out", "resetOr.in0");
        def->connect("self.reset", "resetOr.in1");
        def->connect("resetOr.out", "count.clr");
        def->connect("and.out", "self.overflow");
      }
    });

  /////////////////////////////////
  //*** serializer definition ***//
  /////////////////////////////////

  // on count==0, read in all input values.
  // on every cycle, input<n> is outputted where n=count

  // serializer type
  commonlib->newTypeGen(
    "serializer_type",                          // name for the typegen
    {{"width", c->Int()}, {"rate", c->Int()}},  // generater parameters
    [](Context* c, Values args) {               // Function to compute type
      uint width = args.at("width")->get<int>();
      uint rate = args.at("rate")->get<int>();
      return c->Record(
        {{"en", c->BitIn()},
         {"reset", c->BitIn()},
         {"count", c->Bit()->Arr(width)},
         {"ready", c->Bit()},  // have cycled through all outputs, put new
                               // inputs on this cycle
         {"in", c->BitIn()->Arr(width)->Arr(rate)},
         {"out", c->Bit()->Arr(width)}});
    });

  Generator* serializer = commonlib->newGeneratorDecl(
    "serializer",
    commonlib->getTypeGen("serializer_type"),
    {{"width", c->Int()}, {"rate", c->Int()}});

  serializer->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      uint width = args.at("width")->get<int>();
      uint rate = args.at("rate")->get<int>();
      assert(width > 0);
      assert(rate > 1);
      assert(
        width > num_bits(rate - 1));  // not enough bits in counter for rate

      // get generators
      Namespace* coreirprims = c->getNamespace("coreir");
      Generator* const_gen = coreirprims->getGenerator("const");
      Generator* eq_gen = coreirprims->getGenerator("eq");

      // create hardware
      Const* aBitwidth = Const::make(c, width);
      def->addInstance(
        "counter",
        "commonlib.counter",
        {{"width", aBitwidth},
         {"min", Const::make(c, 0)},
         {"max", Const::make(c, rate - 1)},
         {"inc", Const::make(c, 1)}});
      def->addInstance(
        "muxn",
        "commonlib.muxn",
        {{"width", aBitwidth}, {"N", Const::make(c, rate)}});
      def->addInstance("equal", eq_gen, {{"width", aBitwidth}});
      def->addInstance(
        "zero",
        const_gen,
        {{"width", aBitwidth}},
        {{"value", Const::make(c, BitVector(width, 0))}});
      Values sliceArgs = {{"width", Const::make(c, width)},
                          {"lo", Const::make(c, 0)},
                          {"hi", Const::make(c, num_bits(rate - 1))}};
      def->addInstance("slice", "coreir.slice", sliceArgs);

      // all but input0 are stored in registers
      for (uint i = 1; i < rate; ++i) {
        std::string reg_name = "reg_" + std::to_string(i);
        def->addInstance(
          reg_name,
          "mantle.reg",
          {{"width", aBitwidth}, {"has_en", Const::make(c, true)}},
          {{"init", Const::make(c, width, 0)}});
      }
      def->addInstance("ignoreOverflow", "corebit.term");

      // wire up modules
      def->connect("self.reset", "counter.reset");
      def->connect("equal.out", "self.ready");
      def->connect("self.en", "counter.en");
      def->connect("counter.out", "self.count");
      def->connect("counter.overflow", "ignoreOverflow.in");

      def->connect("counter.out", "slice.in");
      def->connect("slice.out", "muxn.in.sel");

      def->connect("zero.out", "equal.in0");
      def->connect("counter.out", "equal.in1");

      // wire up inputs to regs and mux
      for (uint i = 0; i < rate; ++i) {
        std::string idx = std::to_string(i);
        if (i == 0) { def->connect("self.in.0", "muxn.in.data.0"); }
        else {
          std::string reg_name = "reg_" + idx;
          def->connect("self.in." + idx, reg_name + ".in");
          def->connect(reg_name + ".out", "muxn.in.data." + idx);

          // connect reg enables
          def->connect(reg_name + ".en", "equal.out");
        }
      }

      def->connect("muxn.out", "self.out");
    });

  /////////////////////////////////
  // deserializer definition     //
  /////////////////////////////////

  // on every cycle, input<n> is received where n=count
  // on count==rate-1, output all input values.

  // serializer type
  commonlib->newTypeGen(
    "deserializer_type",                        // name for the typegen
    {{"width", c->Int()}, {"rate", c->Int()}},  // generater parameters
    [](Context* c, Values args) {               // Function to compute type
      uint width = args.at("width")->get<int>();
      uint rate = args.at("rate")->get<int>();
      return c->Record({{"en", c->BitIn()},
                        {"reset", c->BitIn()},
                        {"valid", c->Bit()},  // output is valid
                        {"in", c->BitIn()->Arr(width)},
                        {"out", c->Bit()->Arr(width)->Arr(rate)}});
    });

  Generator* deserializer = commonlib->newGeneratorDecl(
    "deserializer",
    commonlib->getTypeGen("deserializer_type"),
    {{"width", c->Int()}, {"rate", c->Int()}});

  deserializer->setGeneratorDefFromFun(
    [](Context* c, Values args, ModuleDef* def) {
      uint width = args.at("width")->get<int>();
      uint rate = args.at("rate")->get<int>();
      assert(width > 0);
      assert(rate > 1);

      // create hardware
      Const* aBitwidth = Const::make(c, width);
      for (uint i = 0; i < rate - 1; ++i) {
        std::string reg_name = "reg_" + std::to_string(i);
        def->addInstance(
          reg_name,
          "mantle.reg",
          {{"width", aBitwidth}, {"has_en", Const::make(c, true)}},
          {{"init", Const::make(c, width, 0)}});
      }
      // these registers pass along the signal to write to one register
      // this signal is initalized by reset being passed in, and is passed along
      // so that only 1 register is written to in each clock cycle
      // and all reg enables after first with not reset so that, if one reset
      // before an earlier one finishes, the earlier one is aborted
      // the first reg starts with signal 1, the rest with 0
      for (uint i = 0; i < rate - 1; ++i) {
        std::string reg_name = "en_reg_" + std::to_string(i);
        std::string and_name = "en_and_" + std::to_string(i);
        def->addInstance(
          reg_name,
          "mantle.reg",
          {{"width", Const::make(c, 1)}, {"has_en", Const::make(c, true)}},
          {{"init", Const::make(c, 1, i == 0 ? 1 : 0)}});
        def->addInstance(and_name, "corebit.and");
      }
      // this reg is 1 only cycle after last enable reg is 1, to indicate that
      // all registers have been written to in the last cycle
      def->addInstance(
        "validReg",
        "mantle.reg",
        {{"width", Const::make(c, 1)}, {"has_en", Const::make(c, false)}},
        {{"init", Const::make(c, 1, 0)}});
      // use this for driving input to first enable reg
      def->addInstance("firstEnabledOr", "corebit.or");
      // the not to invert the reset
      def->addInstance("resetInvert", "corebit.not");

      def->connect("self.reset", "resetInvert.in");

      // wire up one input to all regs
      for (uint i = 0; i < rate - 1; ++i) {
        std::string idx = std::to_string(i);
        std::string reg_name = "reg_" + idx;
        std::string en_reg_name = "en_reg_" + idx;
        std::string en_and_name = "en_and_" + idx;
        std::string next_en_reg_name = "en_reg_" + std::to_string(i + 1);

        def->connect("self.in", reg_name + ".in");
        def->connect(reg_name + ".out", "self.out." + idx);

        // for every data reg, wire in the enable reg
        def->connect(en_reg_name + ".out.0", reg_name + ".en");
        def->connect("self.en", en_reg_name + ".en");

        // if this is the last reg, wire it's output and the deserializer reset
        // into the input for the first enable reg as if either occurs its a
        // reason for starting cycle again
        if (i == rate - 2) {
          def->connect("self.reset", "firstEnabledOr.in0");
          def->connect(en_reg_name + ".out.0", "firstEnabledOr.in1");
          def->connect(
            "firstEnabledOr.out",
            "en_reg_" + std::to_string(0) + ".in.0");

          // wire up the valid signal, which comes one clock after the last reg
          // is enabled, same cycle as that reg starts emitting the right value
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
      // wire the input to the last output slot, as directly sending that one
      // out so each cycle is 4 clocks, 3 clock ticks
      def->connect("self.in", "self.out." + to_string(rate - 1));
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
  Params reshape_params = {
    {"input_type", CoreIRType::make(c)},
    {"output_type", CoreIRType::make(c)},
  };

  commonlib->newTypeGen(
    "reshape_type",
    reshape_params,
    [](Context* c, Values genargs) {  // Function to compute type
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

      return c->Record({{"in", input_type}, {"out", output_type}});
    });

  Generator* reshape = commonlib->newGeneratorDecl(
    "reshape",
    commonlib->getTypeGen("reshape_type"),
    reshape_params);
  reshape->setGeneratorDefFromFun(
    [](Context* c, Values genargs, ModuleDef* def) {
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
        // for (const auto& input_port : input_idxs) {
        for (int i = input_idxs.size() - 1; i >= 0; --i) {
          assert(i < (int)input_idxs.size());
          auto input_port = input_idxs.at(i);
          input_name += "." + std::to_string(input_port);
        }
        string output_name = "self.out";
        // for (const auto& output_port : output_idxs) {
        for (int i = output_idxs.size() - 1; i >= 0; --i) {
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
            if (dim + 1 < input_idxs.size()) { input_idxs.at(dim + 1) += 1; }
          }
        }

        // increment output index
        output_idxs.at(0) += 1;
        for (size_t dim = 0; dim < output_idxs.size(); ++dim) {
          if (output_idxs.at(dim) >= output_vector.at(dim)) {
            output_idxs.at(dim) = 0;
            if (dim + 1 < output_idxs.size()) { output_idxs.at(dim + 1) += 1; }
          }
        }
      }
    });

  ////////////////////////////////
  //*** transpose definition ***//
  ////////////////////////////////
  Params transpose_params = {
    {"input_type", CoreIRType::make(c)},
  };

  commonlib->newTypeGen(
    "transpose_type",
    transpose_params,
    [](Context* c, Values genargs) {  // Function to compute type
      Type* input_type = genargs.at("input_type")->get<Type*>();

      return c->Record({{"in", input_type}, {"out", c->Flip(input_type)}});
    });

  Generator* transpose = commonlib->newGeneratorDecl(
    "transpose",
    commonlib->getTypeGen("transpose_type"),
    transpose_params);
  transpose->setGeneratorDefFromFun(
    [](Context* c, Values genargs, ModuleDef* def) {
      auto input_type = genargs.at("input_type")->get<Type*>();
      auto input_dims = get_dims(input_type);
      input_dims.erase(input_dims.begin());

      // determine number of ports
      int num_ports = 1;
      for (const auto& port_length : input_dims) { num_ports *= port_length; }

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
            if (dim + 1 < port_idxs.size()) { port_idxs.at(dim + 1) += 1; }
          }
        }
      }
    });

  ////////////////////////////////////////
  //*** transpose reshape definition ***//
  ////////////////////////////////////////

  Generator* transpose_reshape = commonlib->newGeneratorDecl(
    "transpose_reshape",
    commonlib->getTypeGen("reshape_type"),
    reshape_params);
  transpose_reshape->setGeneratorDefFromFun(
    [](Context* c, Values genargs, ModuleDef* def) {
      auto input_type = genargs.at("input_type")->get<Type*>();

      auto self = def->sel("self");
      auto transpose = def->addInstance(
        "transpose",
        "commonlib.transpose",
        {{"input_type", Const::make(c, input_type)}});
      auto reshape = def->addInstance("reshape", "commonlib.reshape", genargs);

      def->connect(self->sel("in"), transpose->sel("in"));
      def->connect(transpose->sel("out"), reshape->sel("in"));
      def->connect(reshape->sel("out"), self->sel("out"));
    });

  ////////////////////////////////////////////
  //*** accumulation register definition ***//
  ////////////////////////////////////////////
  // connections: input:      accumulated data
  //                          bias value
  //                          input valid
  //                          reset
  //
  //              output:     partial/final data
  //                          valid
  //
  //              parameters: number of reduction iterations
  //
  commonlib->newTypeGen(
    "accumulation_register_type",                     // name for the typegen
    {{"width", c->Int()}, {"iterations", c->Int()}},  // generater parameters
    [](Context* c, Values args) {  // Function to compute type
      uint width = args.at("width")->get<int>();
      uint iterations = args.at("iterations")->get<int>();
      assert(width > 0);
      assert(iterations > 1);

      return c->Record({{"in_valid", c->BitIn()},
                        {"reset", c->BitIn()},
                        {"bias", c->BitIn()->Arr(width)},
                        {"in_data", c->BitIn()->Arr(width)},
                        {"out_data", c->Bit()->Arr(width)},
                        {"valid", c->Bit()}});
    });

  Generator* accum_reg = commonlib->newGeneratorDecl(
    "accumulation_register",
    commonlib->getTypeGen("accumulation_register_type"),
    {{"width", c->Int()}, {"iterations", c->Int()}});

  accum_reg->setGeneratorDefFromFun([](
                                      Context* c,
                                      Values args,
                                      ModuleDef* def) {
    uint width = args.at("width")->get<int>();
    uint iterations = args.at("iterations")->get<int>();

    Const* aBitwidth = Const::make(c, width);
    Values bitwidthParams = {{"width", aBitwidth}};

    Values counter_args = {{"width", Const::make(c, width)},
                           {"min", Const::make(c, 0)},
                           {"max", Const::make(c, iterations - 1)},
                           {"inc", Const::make(c, 1)}};

    def->addInstance("phase_counter", "commonlib.counter", counter_args);
    Values const_value = {
      {"value", Const::make(c, BitVector(width, iterations - 1))}};
    def->addInstance(
      "output_phase_value",
      "coreir.const",
      bitwidthParams,
      const_value);

    def->addInstance("invalid_bit", "corebit.reg");
    def->addInstance("valid_mux", "corebit.mux");

    Values reg_configargs = {{"init", Const::make(c, BitVector(width, 0))}};
    def->addInstance("accum_reg", "mantle.reg", bitwidthParams, reg_configargs);

    def->addInstance("input_mux", "coreir.mux", bitwidthParams);
    def->addInstance("phase_sel", "coreir.eq", bitwidthParams);
    def->addInstance("accum_adder", "coreir.add", bitwidthParams);

    // create output phase logic
    def->connect("self.in_valid", "phase_counter.en");
    def->connect("self.reset", "phase_counter.reset");
    def->connect("phase_sel.in0", "phase_counter.out");
    def->connect("phase_sel.in1", "output_phase_value.out");

    // create valid logic
    def->connect("valid_mux.in0", "invalid_bit.out");
    def->connect("valid_mux.in1", "self.in_valid");
    def->connect("valid_mux.sel", "phase_sel.out");
    def->connect("valid_mux.out", "self.valid");

    // create output data
    def->connect("accum_adder.in0", "self.in_data");
    def->connect("accum_adder.in1", "accum_reg.out");
    def->connect("accum_adder.out", "self.out_data");
    def->connect("input_mux.in1", "self.bias");
    def->connect("input_mux.in0", "accum_adder.out");
    def->connect("input_mux.sel", "phase_sel.out");
    def->connect("input_mux.out", "accum_reg.in");
  });

  return commonlib;
}

COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(commonlib)
