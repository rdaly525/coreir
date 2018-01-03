

using namespace CoreIR;
using namespace std;
void CoreIRLoadVerilog_coreir(Context* c) {
  std::map<std::string,std::map<std::string,std::string>> coreVMap({
    {"unary",{
      {"wire","in"},
      {"not","~in"},
      {"neg","-in"}
    }},
    {"unaryReduce",{
      {"andr","&in"},
      {"orr","|in"},
      {"xorr","^in"}
    }},
    {"binary",{
      {"and","in0 & in1"},
      {"or","in0 | in1"},
      {"xor","in0 ^ in1"},
      {"shl","in0 << in1"},
      {"lshr","in0 >> in1"},
      {"ashr","$signed(in0) >>> in1"},
      {"add","in0 + in1"},
      {"sub","in0 - in1"},
      {"mul","in0 * in1"},
      {"udiv","in0 / in1"},
      {"sdiv","$signed(in0) / $signed(in1)"}
    }},
    {"binaryReduce",{
      {"eq","in0 == in1"},
      {"neq","in0 != in1"},
      {"slt","$signed(in0) < $signed(in1)"},
      {"sgt","$signed(in0) > $signed(in1)"},
      {"sle","$signed(in0) <= $signed(in1)"},
      {"sge","$signed(in0) >= $signed(in1)"},
      {"ult","in0 < in1"},
      {"ugt","in0 > in1"},
      {"ule","in0 <= in1"},
      {"uge","in0 >= in1"}
    }},
    {"other",{
      {"mux","sel ? in1 : in0"},
      {"slice","in[hi-1:lo]"},
      {"concat","{in0,in1}"},
      {"zext","{(width_out-width_in){1'b0},in}"},
      {"sext","{(width_out-width_in){in[width_in-1]},in}"},
      {"const","value"}
      //{"term",""}
      //{"reg",""}, 
      //{"mem",""}, 
    }}
  });
 
  
  std::map<std::string,std::vector<std::string>> coreIMap({
    {"unary",{
      "input [width-1:0] in",
      "output [width-1:0] out"
    }},
    {"unaryReduce",{
      "input [width-1:0] in",
      "output out"
    }},
    {"binary",{
      "input [width-1:0] in0",
      "input [width-1:0] in1",
      "output [width-1:0] out"
    }},
    {"binaryReduce",{
      "input [width-1:0] in0",
      "input [width-1:0] in1",
      "output out"
    }},
    {"mux",{
      "input [width-1:0] in0",
      "input [width-1:0] in1",
      "input sel",
      "output [width-1:0] out"
    }},
    {"slice",{
      "input [width-1:0] in",
      "output [hi-lo-1:0] out"
    }},
    {"concat",{
      "input [width0-1:0] in0",
      "input [width1-1:0] in1",
      "output [width0+width1-1:0] out"
    }},
    {"zext",{
      "input [width_in-1:0] in",
      "output [width_out-1:0] out"
    }},
    {"sext",{
      "input [width_in-1:0] in",
      "output [width_out-1:0] out"
    }},
    {"const",{"output [width-1:0] out"}},
    {"term",{"input [width-1:0] in"}},
    {"reg",{
      "input clk",
      "input [width-1:0] in",
      "output [width-1:0] out"
    }},
    {"regrst",{
      "input clk",
      "input rst",
      "input [width-1:0] in",
      "output [width-1:0] out"
    }},
    {"mem",{
      "input clk",
      "input [width-1:0] wdata",
      "input [$clog2(depth)-1:0] waddr",
      "input wen",
      "output [width-1:0] rdata",
      "input [$clog2(depth)-1:0] raddr"
    }}
  });

  Namespace* core = c->getNamespace("coreir");
  for (auto it0 : coreVMap) {
    for (auto it1 : it0.second) {
      string op = it1.first;
      string vbody = it1.second;
      json vjson;
      vjson["prefix"] = "coreir_";
      vjson["definition"] = "  assign out = " + vbody + ";";
      if (it0.first!="other") {
        ASSERT(coreIMap.count(it0.first),"missing" + it0.first);
        vjson["interface"] = coreIMap.at(it0.first);
      }
      else {
        ASSERT(coreIMap.count(it1.first),"missing" + it1.first);
        vjson["interface"] = coreIMap.at(it1.first);
      }
      core->getGenerator(op)->getMetaData()["verilog"] = vjson;
    }
  }

  core->getGenerator("const")->getMetaData()["verilog"]["parameters"] = {"value"};
  
  {
    //Term
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["interface"] = coreIMap["term"];
    vjson["definition"] = "";
    core->getGenerator("term")->getMetaData()["verilog"] = vjson;
  }
  {
    //regrst
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["parameters"] = {"init"};
    vjson["interface"] = coreIMap.at("regrst");
    vjson["definition"] = ""
    "reg [width-1:0] outReg;\n"
    "always @(posedge clk, negedge rst) begin\n"
    "  if (!rst) outReg <= init;\n"
    "  else outReg <= in;\n"
    "end\n"
    "assign out = outReg;";
    core->getGenerator("regrst")->getMetaData()["verilog"] = vjson;
  }
  {
    //reg
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["parameters"] = {"init"};
    vjson["interface"] = coreIMap.at("reg");
    vjson["definition"] = ""
    "reg [width-1:0] outReg=init;\n"
    "always @(posedge clk) begin\n"
    "  outReg <= in;\n"
    "end\n"
    "assign out = outReg;";
    core->getGenerator("reg")->getMetaData()["verilog"] = vjson;
  }

  {
    //mem
    json vjson;
    vjson["interface"] = coreIMap["mem"];
    vjson["definition"] = ""
    "reg [width-1:0] data[depth];\n"
    "always @(posedge clk) begin\n"
    "  if (wen) begin\n"
    "    data[waddr] <= wdata;\n"
    "  end\n"
    "end\n"
    "assign rdata = data[raddr];";
    core->getGenerator("mem")->getMetaData()["verilog"] = vjson;
  } 
}
