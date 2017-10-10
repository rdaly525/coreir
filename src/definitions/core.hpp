

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
      {"slice","in[hi-1:lo]"},
      {"concat","{in0,in1}"},
      {"const","init"}
      //{"term",""}
      //{"reg",""}, 
      //{"mem",""}, 
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
      core->getGenerator(op)->getMetaData()["verilog"] = vjson;
    }
  }

  //Term
  json vjson;
  vjson["prefix"] = "coreir_";
  vjson["definition"] = "";
  core->getGenerator("term")->getMetaData()["verilog"] = vjson;
  
  //reg
  vjson["definition"] = ""
  "reg [width-1:0] outReg;\n"
  "always @(posedge clk, negedge rst) begin\n"
  "  if (!rst) outReg <= init;\n"
  "  else outReg <= in;\n"
  "end\n"
  "assign out = outReg;";

  core->getGenerator("reg")->getMetaData()["verilog"] = vjson;
  
  //mem
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
