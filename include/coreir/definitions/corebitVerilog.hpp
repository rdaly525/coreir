

using namespace CoreIR;
using namespace std;
void CoreIRLoadVerilog_corebit(Context* c) {
  std::map<std::string,std::map<std::string,std::string>> bitVMap({
    {"unary",{
      {"wire","in"},
      {"not","~in"},
    }},
    {"binary",{
      {"and","in0 & in1"},
      {"or","in0 | in1"},
      {"xor","in0 ^ in1"},
    }},
    {"other",{
      {"mux","sel ? in1 : in0"},
      {"concat","{in0, in1}"},
      {"const","value"},
      {"term",""},
      {"tribuf","en ? in : 1'bz"},
      {"ibuf","in"},
    }}
  });
 
  
  std::map<std::string,std::vector<std::string>> bitIMap({
    {"unary",{
      "input in",
      "output out"
    }},
    {"binary",{
      "input in0",
      "input in1",
      "output out"
    }},
    {"mux",{
      "input in0",
      "input in1",
      "input sel",
      "output out"
    }},
    {"concat",{
      "input in0",
      "input in1",
      "output [1:0] out"
    }},
    {"const",{"output out"}},
    {"term",{"input in"}},
    {"tribuf",{
      "input in",
      "input en",
      "inout out"
    }},
    {"ibuf",{
      "inout in",
      "output out"
    }},
    {"reg",{
      "input clk",
      "input in",
      "output out"
    }},
    {"reg_arst",{
      "input clk",
      "input in",
      "input arst",
      "output out"
    }}
  });

  Namespace* bit = c->getNamespace("corebit");
  for (auto it0 : bitVMap) {
    for (auto it1 : it0.second) {
      string op = it1.first;
      string vbody = it1.second;
      json vjson;
      vjson["prefix"] = "corebit_";
      vjson["definition"] = "  assign out = " + vbody + ";";
      if (it0.first!="other") {
        ASSERT(bitIMap.count(it0.first),"missing" + it0.first);
        vjson["interface"] = bitIMap.at(it0.first);
      }
      else {
        ASSERT(bitIMap.count(it1.first),"missing" + it1.first);
        vjson["interface"] = bitIMap.at(it1.first);
      }
      bit->getModule(op)->getMetaData()["verilog"] = vjson;
    }
  }

  bit->getModule("const")->getMetaData()["verilog"]["parameters"] = {"value"};
  
  {
    //Term
    json vjson;
    vjson["prefix"] = "corebit_";
    vjson["interface"] = bitIMap["term"];
    vjson["definition"] = "";
    bit->getModule("term")->getMetaData()["verilog"] = vjson;
  }
  {
    //reg
    json vjson;
    vjson["prefix"] = "corebit_";
    vjson["parameters"] = {"init"};
    vjson["interface"] = bitIMap.at("reg");
    vjson["definition"] = ""
    "reg outReg = init;\n"
    "always @(posedge clk) begin\n"
    "  outReg <= in;\n"
    "end\n"
    "assign out = outReg;";
    bit->getModule("reg")->getMetaData()["verilog"] = vjson;
  }
  {
    //reg_arst
    json vjson;
    vjson["prefix"] = "corebit_";
    vjson["parameters"] = {"init","arst_posedge"};
    vjson["interface"] = bitIMap.at("reg_arst");
    vjson["definition"] = ""
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
    bit->getModule("reg_arst")->getMetaData()["verilog"] = vjson;
  }
}
