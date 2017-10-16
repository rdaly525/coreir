

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
      {"const","value"},
      {"term",""}
      //{"reg",""}, TODO
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
    {"const",{"output out"}},
    {"term",{"input in"}},
    {"dff",{
      "input clk",
      "input in",
      "input rst",
      "output out"
    }}
    //{"reg",{
    //  "input clk",
    //  "input [width-1:0] in",
    //  "output [width-1:0] out"
    //}},
    //{"regrst",{
    //  "input clk",
    //  "input rst",
    //  "input [width-1:0] in",
    //  "output [width-1:0] out"
    //}},
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
    //dff
    json vjson;
    vjson["parameters"] = {"init"};
    vjson["interface"] = bitIMap.at("dff");
    vjson["definition"] = ""
    "reg outReg;\n"
    "always @(posedge clk) begin\n"
    "  if (!rst) outReg <= init;\n"
    "  else outReg <= in;\n"
    "end\n"
    "assign out = outReg;";
    bit->getModule("dff")->getMetaData()["verilog"] = vjson;
  }
  //{
  //  //regrst
  //  json vjson;
  //  vjson["parameters"] = {"init"};
  //  vjson["interface"] = bitIMap.at("regrst");
  //  vjson["definition"] = ""
  //  "reg [width-1:0] outReg;\n"
  //  "always @(posedge clk, negedge rst) begin\n"
  //  "  if (!rst) outReg <= init;\n"
  //  "  else outReg <= in;\n"
  //  "end\n"
  //  "assign out = outReg;";
  //  bit->getModule("regrst")->getMetaData()["verilog"] = vjson;
  //}
  //{
  //  //reg
  //  json vjson;
  //  vjson["interface"] = bitIMap.at("reg");
  //  vjson["definition"] = ""
  //  "reg [width-1:0] outReg;\n"
  //  "always @(posedge clk) begin\n"
  //  "  outReg <= in;\n"
  //  "end\n"
  //  "assign out = outReg;";
  //  bit->getModule("reg")->getMetaData()["verilog"] = vjson;
  //}
}
