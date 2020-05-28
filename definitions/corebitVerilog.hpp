using namespace CoreIR;
using namespace std;
void CoreIRLoadVerilog_corebit(Context* c) {
  using VerilogLoaderT = std::map<
    std::string,
    std::map<
      std::string,
      std::
        pair<std::string, std::function<std::unique_ptr<vAST::Expression>()>>>>;

  VerilogLoaderT bitVMap{
    {
      "unary",
      {
        {"wire", {"in", []() { return vAST::make_id("in"); }}},
        {
          "not",
          {
            "~in",
            []() {
              return std::make_unique<vAST::UnaryOp>(
                vAST::make_id("in"),
                vAST::UnOp::INVERT);
            },
          },
        },
      },
    },
    {
      "binary",
      {
        {
          "and",
          {
            "in0 & in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::AND,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "or",
          {
            "in0 | in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::OR,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "xor",
          {
            "in0 ^ in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::XOR,
                vAST::make_id("in1"));
            },
          },
        },
      },
    },
    {
      "other",
      {
        {
          "mux",
          {
            "sel ? in1 : in0",
            []() {
              return std::make_unique<vAST::TernaryOp>(
                vAST::make_id("sel"),
                vAST::make_id("in1"),
                vAST::make_id("in0"));
            },
          },
        },
        {
          "concat",
          {"{in1,in0}",
           []() {
             return std::make_unique<vAST::Concat>(make_args({"in1", "in0"}));
           }},
        },
        {"const", {"value", []() { return vAST::make_id("value"); }}},
        {
          "tribuf",
          {
            "en ? in : 'hz",
            []() {
              return std::make_unique<vAST::TernaryOp>(
                vAST::make_id("en"),
                vAST::make_id("in"),
                std::make_unique<vAST::NumericLiteral>("z", vAST::Radix::HEX));
            },
          },
        },
        {"ibuf", {"in", []() { return vAST::make_id("in"); }}},
      },
    },
  };

  std::map<std::string, std::vector<std::string>> bitIMap(
    {{"unary", {"input in", "output out"}},
     {"binary", {"input in0", "input in1", "output out"}},
     {"mux", {"input in0", "input in1", "input sel", "output out"}},
     {"concat", {"input in0", "input in1", "output [1:0] out"}},
     {"const", {"output out"}},
     {"term", {"input in"}},
     {"undriven", {"output out"}},
     {"tribuf", {"input in", "input en", "inout out"}},
     {"ibuf", {"inout in", "output out"}},
     {"reg", {"input clk", "input in", "output out"}},
     {"reg_arst", {"input clk", "input in", "input arst", "output out"}}});

  Namespace* bit = c->getNamespace("corebit");
  for (auto it0 : bitVMap) {
    for (auto it1 : it0.second) {
      string op = it1.first;
      string vbody = it1.second.first;
      json vjson;
      vjson["prefix"] = "corebit_";
      vjson["definition"] = "  assign out = " + vbody + ";";
      vjson["inlineable"] = true;
      if (it0.first != "other") {
        ASSERT(bitIMap.count(it0.first), "missing" + it0.first);
        vjson["interface"] = bitIMap.at(it0.first);
      }
      else {
        ASSERT(bitIMap.count(it1.first), "missing" + it1.first);
        vjson["interface"] = bitIMap.at(it1.first);
      }
      vjson["primitive_type"] = it0.first;
      bit->getModule(op)->setPrimitiveExpressionLambda(it1.second.second);
      bit->getModule(op)->getMetaData()["verilog"] = vjson;
    }
  }

  // bit->getModule("const")->getMetaData()["verilog"]["parameters"] =
  // {"value"};

  {
    // Term
    json vjson;
    vjson["prefix"] = "corebit_";
    vjson["interface"] = bitIMap["term"];
    vjson["definition"] = "";
    bit->getModule("term")->getMetaData()["verilog"] = vjson;
  }
  {
    // Undriven
    json vjson;
    vjson["prefix"] = "corebit_";
    vjson["interface"] = bitIMap["undriven"];
    vjson["definition"] = "";
    bit->getModule("undriven")->getMetaData()["verilog"] = vjson;
  }
  {
    // reg
    json vjson;
    vjson["prefix"] = "corebit_";
    // vjson["parameters"] = {"init"};
    vjson["interface"] = bitIMap.at("reg");
    vjson["definition"] =
      ""
      "reg outReg = init;\n"
      "always @(posedge clk) begin\n"
      "  outReg <= in;\n"
      "end\n"
      "assign out = outReg;";
    vjson["verilator_debug_definition"] =
      ""
      "reg outReg/*verilator public*/ = init;\n"
      "always @(posedge clk) begin\n"
      "  outReg <= in;\n"
      "end\n"
      "assign out = outReg;";
    bit->getModule("reg")->getMetaData()["verilog"] = vjson;
  }
  {
    // reg_arst
    json vjson;
    vjson["prefix"] = "corebit_";
    // vjson["parameters"] = {"init","arst_posedge"};
    vjson["interface"] = bitIMap.at("reg_arst");
    vjson["definition"] =
      ""
      "reg outReg;\n"
      "wire real_rst;\n"
      "assign real_rst = arst_posedge ? arst : ~arst;\n"
      "wire real_clk;\n"
      "assign real_clk = clk_posedge ? clk : ~clk;\n"
      "always @(posedge real_clk, posedge real_rst) begin\n"
      "  if (real_rst) outReg <= init;\n"
      "  else outReg <= in;\n"
      "end\n"
      "assign out = outReg;";
    vjson["verilator_debug_definition"] =
      ""
      "reg outReg/*verilator public*/;\n"
      "wire real_rst;\n"
      "assign real_rst = arst_posedge ? arst : ~arst;\n"
      "wire real_clk;\n"
      "assign real_clk = clk_posedge ? clk : ~clk;\n"
      "always @(posedge real_clk, posedge real_rst) begin\n"
      "  if (real_rst) outReg <= init;\n"
      "  else outReg <= in;\n"
      "end\n"
      "assign out = outReg;";
    bit->getModule("reg_arst")->getMetaData()["verilog"] = vjson;
  }
}
