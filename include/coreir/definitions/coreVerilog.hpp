#include "verilogAST.hpp"
#include "coreir/definitions/memoryVerilog.hpp"

namespace vAST = verilogAST;

std::vector<std::unique_ptr<vAST::Expression>> make_args(
  std::vector<std::string> args) {
  std::vector<std::unique_ptr<vAST::Expression>> arg_ptrs;
  for (auto a : args) { arg_ptrs.push_back(vAST::make_id(a)); }
  return arg_ptrs;
}

std::vector<std::unique_ptr<vAST::Expression>> make_ext_args(
  std::vector<std::unique_ptr<vAST::Expression>> args) {
  return args;
}

std::unique_ptr<vAST::CallExpr> make_signed_call(const char* id) {
  std::vector<std::unique_ptr<vAST::Expression>> args;
  args.push_back(vAST::make_id(std::string(id)));
  return std::make_unique<vAST::CallExpr>("$signed", std::move(args));
}

using namespace CoreIR;
using namespace std;
void CoreIRLoadVerilog_coreir(Context* c) {

  using VerilogLoaderT = std::map<
    std::string,
    std::map<
      std::string,
      std::
        pair<std::string, std::function<std::unique_ptr<vAST::Expression>()>>>>;

  VerilogLoaderT coreVMap{
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
        {
          "neg",
          {"-in",
           []() {
             return std::make_unique<vAST::UnaryOp>(
               vAST::make_id("in"),
               vAST::UnOp::MINUS);
           }},
        },
      },
    },
    {
      "unaryReduce",
      {
        {
          "andr",
          {"&in",
           []() {
             return std::make_unique<vAST::UnaryOp>(
               vAST::make_id("in"),
               vAST::UnOp::AND);
           }},
        },
        {
          "orr",
          {
            "|in",
            []() {
              return std::make_unique<vAST::UnaryOp>(
                vAST::make_id("in"),
                vAST::UnOp::OR);
            },
          },
        },
        {
          "xorr",
          {
            "^in",
            []() {
              return std::make_unique<vAST::UnaryOp>(
                vAST::make_id("in"),
                vAST::UnOp::XOR);
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
        {
          "shl",
          {
            "in0 << in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::LSHIFT,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "lshr",
          {
            "in0 >> in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::RSHIFT,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "ashr",
          {
            "$signed(in0) >>> in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                make_signed_call("in0"),
                vAST::BinOp::ARSHIFT,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "add",
          {
            "in0 + in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::ADD,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "sub",
          {
            "in0 - in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::SUB,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "mul",
          {
            "in0 * in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::MUL,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "udiv",
          {
            "in0 / in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::DIV,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "sdiv",
          {
            "$signed(in0) / $signed(in1)",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                make_signed_call("in0"),
                vAST::BinOp::DIV,
                make_signed_call("in1"));
            },
          },
        },
      },
    },
    {
      "binaryReduce",
      {
        {
          "eq",
          {
            "in0 == in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::EQ,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "neq",
          {
            "in0 != in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::NEQ,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "slt",
          {
            "$signed(in0) < $signed(in1)",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                make_signed_call("in0"),
                vAST::BinOp::LT,
                make_signed_call("in1"));
            },
          },
        },
        {
          "sgt",
          {
            "$signed(in0) > $signed(in1)",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                make_signed_call("in0"),
                vAST::BinOp::GT,
                make_signed_call("in1"));
            },
          },
        },
        {
          "sle",
          {
            "$signed(in0) <= $signed(in1)",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                make_signed_call("in0"),
                vAST::BinOp::LTE,
                make_signed_call("in1"));
            },
          },
        },
        {
          "sge",
          {
            "$signed(in0) >= $signed(in1)",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                make_signed_call("in0"),
                vAST::BinOp::GTE,
                make_signed_call("in1"));
            },
          },
        },
        {
          "ult",
          {
            "in0 < in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::LT,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "ugt",
          {
            "in0 > in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::GT,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "ule",
          {
            "in0 <= in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::LTE,
                vAST::make_id("in1"));
            },
          },
        },
        {
          "uge",
          {
            "in0 >= in1",
            []() {
              return std::make_unique<vAST::BinaryOp>(
                vAST::make_id("in0"),
                vAST::BinOp::GTE,
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
          "slice",
          {
            "in[hi-1:lo]",
            []() {
              return std::make_unique<vAST::Slice>(
                vAST::make_id("in"),
                vAST::make_binop(
                  vAST::make_id("hi"),
                  vAST::BinOp::SUB,
                  vAST::make_num("1")),
                vAST::make_id("lo"));
            },
          },
        },
        {
          "concat",
          {
            "{in1,in0}",
            []() {
              return std::make_unique<vAST::Concat>(make_args({"in1", "in0"}));
            },
          },
        },
        {
          "zext",
          {
            "{{(width_out-width_in){1'b0},},in}",
            []() {
              // Can't use initializer list of vector of unique ptrs, so we
              // explicitly construct it
              std::vector<std::unique_ptr<vAST::Expression>> zext_args;
              zext_args.push_back(std::make_unique<vAST::Replicate>(
                vAST::make_binop(
                  vAST::make_id("width_out"),
                  vAST::BinOp::SUB,
                  vAST::make_id("width_in")),
                std::make_unique<vAST::NumericLiteral>(
                  "0",
                  1,
                  false,
                  vAST::Radix::BINARY)));
              zext_args.push_back(vAST::make_id("in"));
              return std::make_unique<vAST::Concat>(std::move(zext_args));
            },
          },
        },
        {
          "sext",
          {
            "{{(width_out-width_in){in[width_in-1]}},in}",
            []() {
              // Can't use initializer list of vector of unique ptrs, so we
              // explicitly construct it
              std::vector<std::unique_ptr<vAST::Expression>> sext_args;
              sext_args.push_back(std::make_unique<vAST::Replicate>(
                vAST::make_binop(
                  vAST::make_id("width_out"),
                  vAST::BinOp::SUB,
                  vAST::make_id("width_in")),
                std::make_unique<vAST::Index>(
                  vAST::make_id("in"),
                  vAST::make_binop(
                    vAST::make_id("width_in"),
                    vAST::BinOp::SUB,
                    vAST::make_num("1")))));
              sext_args.push_back(vAST::make_id("in"));
              return std::make_unique<vAST::Concat>(std::move(sext_args));
            },
          },
        },
        {"strip", {"in", []() { return vAST::make_id("in"); }}},
        {"wrap", {"in", []() { return vAST::make_id("in"); }}},
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
        {"ibuf", {"in", []() { return vAST::make_id("in"); }}}
        //{"term",""}
        //{"reg",""},
        //{"mem",""},
      },
    },
  };

  std::map<std::string, std::vector<std::string>> coreIMap{
    {"unary", {"input [width-1:0] in", "output [width-1:0] out"}},
    {"unaryReduce", {"input [width-1:0] in", "output out"}},
    {
      "binary",
      {
        "input [width-1:0] in0",
        "input [width-1:0] in1",
        "output [width-1:0] out",
      },
    },
    {
      "binaryReduce",
      {"input [width-1:0] in0", "input [width-1:0] in1", "output out"},
    },
    {
      "mux",
      {
        "input [width-1:0] in0",
        "input [width-1:0] in1",
        "input sel",
        "output [width-1:0] out",
      },
    },
    {
      "slice",
      {"input [width-1:0] in", "output [hi-lo-1:0] out"},
    },
    {
      "concat",
      {
        "input [width0-1:0] in0",
        "input [width1-1:0] in1",
        "output [width0+width1-1:0] out",
      },
    },
    {"zext", {"input [width_in-1:0] in", "output [width_out-1:0] out"}},
    {"sext", {"input [width_in-1:0] in", "output [width_out-1:0] out"}},
    {"strip", {"input in", "output out"}},
    {"wrap", {"input in", "output out"}},
    {"const", {"output [width-1:0] out"}},
    {"term", {"input [width-1:0] in"}},
    {"undriven", {"output [width-1:0] out"}},
    {"tribuf", {"input [width-1:0] in", "input en", "inout out"}},
    {"ibuf", {"inout [width-1:0] in", "output [width-1:0] out"}},
    {"reg", {"input clk", "input [width-1:0] in", "output [width-1:0] out"}},
    {
      "reg_arst",
      {
        "input clk",
        "input arst",
        "input [width-1:0] in",
        "output [width-1:0] out",
      },
    }
  };

  Namespace* core = c->getNamespace("coreir");
  for (auto it0 : coreVMap) {
    for (auto it1 : it0.second) {
      string op = it1.first;
      string vbody = it1.second.first;
      json vjson;
      vjson["prefix"] = "coreir_";
      vjson["definition"] = "  assign out = " + vbody + ";";
      vjson["inlineable"] = true;
      if (it0.first != "other") {
        ASSERT(coreIMap.count(it0.first), "missing" + it0.first);
        vjson["interface"] = coreIMap.at(it0.first);
      }
      else {
        ASSERT(coreIMap.count(it1.first), "missing" + it1.first);
        vjson["interface"] = coreIMap.at(it1.first);
      }
      vjson["primitive_type"] = it0.first;
      core->getGenerator(op)->getMetaData()["verilog"] = vjson;
      core->getGenerator(op)->setPrimitiveExpressionLambda(it1.second.second);
    }
  }

  core->getGenerator("const")->getMetaData()["verilog"]["parameters"] = {
    "value"};

  {
    // Term
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["interface"] = coreIMap["term"];
    vjson["definition"] = "";
    core->getGenerator("term")->getMetaData()["verilog"] = vjson;
  }
  {
    // Undriven
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["interface"] = coreIMap["undriven"];
    vjson["definition"] = "";
    core->getGenerator("undriven")->getMetaData()["verilog"] = vjson;
  }
  {
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["parameters"] = {"init", "arst_posedge", "clk_posedge"};
    vjson["interface"] = coreIMap.at("reg_arst");
    vjson["definition"] =
      ""
      "  reg [width-1:0] outReg;\n"
      "  wire real_rst;\n"
      "  assign real_rst = arst_posedge ? arst : ~arst;\n"
      "  wire real_clk;\n"
      "  assign real_clk = clk_posedge ? clk : ~clk;\n"
      "  always @(posedge real_clk, posedge real_rst) begin\n"
      "    if (real_rst) outReg <= init;\n"
      "    else outReg <= in;\n"
      "  end\n"
      "  assign out = outReg;";
    vjson["verilator_debug_definition"] =
      ""
      "  reg [width-1:0] outReg/*verilator public*/;\n"
      "  wire real_rst;\n"
      "  assign real_rst = arst_posedge ? arst : ~arst;\n"
      "  wire real_clk;\n"
      "  assign real_clk = clk_posedge ? clk : ~clk;\n"
      "  always @(posedge real_clk, posedge real_rst) begin\n"
      "    if (real_rst) outReg <= init;\n"
      "    else outReg <= in;\n"
      "  end\n"
      "  assign out = outReg;";
    core->getGenerator("reg_arst")->getMetaData()["verilog"] = vjson;
  }
  {
    // reg
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["parameters"] = {"init", "clk_posedge"};
    vjson["interface"] = coreIMap.at("reg");
    vjson["definition"] =
      ""
      "  reg [width-1:0] outReg=init;\n"
      "  wire real_clk;\n"
      "  assign real_clk = clk_posedge ? clk : ~clk;\n"
      "  always @(posedge real_clk) begin\n"
      "    outReg <= in;\n"
      "  end\n"
      "  assign out = outReg;";
    vjson["verilator_debug_definition"] =
      ""
      "  reg [width-1:0] outReg/*verilator public*/=init;\n"
      "  wire real_clk;\n"
      "  assign real_clk = clk_posedge ? clk : ~clk;\n"
      "  always @(posedge real_clk) begin\n"
      "    outReg <= in;\n"
      "  end\n"
      "  assign out = outReg;";
    core->getGenerator("reg")->getMetaData()["verilog"] = vjson;
  }

  {
    // mem
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["interface"] = generateMemoryVerilogInterface(false);
    vjson["parameters"] = {"has_init"};
    vjson["definition"] = generateMemoryVerilogBody(false, false, true);
    vjson["verilator_debug_definition"] = generateMemoryVerilogBody(true, false, true);
    core->getGenerator("mem")->getMetaData()["verilog"] = vjson;
  }
}
