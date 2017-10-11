

using namespace CoreIR;
using namespace std;
void CoreIRLoadFirrtl_coreir(Context* c) {
  std::map<std::string,std::map<std::string,std::vector<std::string>>> coreFMap({
    {"unary",{
      {"wire",{"out <= in"}},
      {"not",{"out <= not(in)"}},
      {"neg",{"out <= neg(in)"}}
    }},
    {"unaryReduce",{
      {"andr",{"out <= andr(in)"}},
      {"orr",{"out <= orr(in)"}},
      {"xorr",{"out <= xorr(in)"}}
    }},
    {"binary",{
      {"and",{"out <= and(in0,in1)"}},
      {"or",{"out <= or(in0,in1)"}},
      {"xor",{"out <= xor(in0,in1)"}},
      {"shl",{"out <= dshl(in0,in1)"}}, //TODO probably should bit select from in1?
      {"lshr",{"out <= dshr(in0,in1)"}},
      {"ashr",{"wire in0_s : SInt","in0_s <= toSInt(in0)","out <= dshr(in0_s,in1)"}},
      {"add",{"out <= add(in0,in1)"}},
      {"sub",{"out <= sub(in0,in1)"}},
      {"mul",{"out <= mul(in0,in1)"}},
      {"udiv",{"out <= div(in0,in1)"}},
      {"sdiv",{"wire in0_s : SInt","wire in1_s : SInt","in0_s <= asSInt(in0)","in1_s <= asSInt(in1)","out <= div(in0_s,in1_s)"}},
    }},
    {"binaryReduce",{
      {"eq",{"out <= eq(in0,in1)"}},
      {"neq",{"out <= neq(in0,in1)"}},
      {"slt",{"wire in0_s : SInt","wire in1_s : SInt","in0_s <= asSInt(in0)","in1_s <= asSInt(in1)","out <= lt(in0_s,in1_s)"}},
      {"sgt",{"wire in0_s : SInt","wire in1_s : SInt","in0_s <= asSInt(in0)","in1_s <= asSInt(in1)","out <= gt(in0_s,in1_s)"}},
      {"sle",{"wire in0_s : SInt","wire in1_s : SInt","in0_s <= asSInt(in0)","in1_s <= asSInt(in1)","out <= leq(in0_s,in1_s)"}},
      {"sge",{"wire in0_s : SInt","wire in1_s : SInt","in0_s <= asSInt(in0)","in1_s <= asSInt(in1)","out <= geq(in0_s,in1_s)"}},
      {"ult",{"out <= lt(in0,in1)"}},
      {"ugt",{"out <= gt(in0,in1)"}},
      {"ule",{"out <= leq(in0,in1)"}},
      {"uge",{"out <= geq(in0,in1)"}},
    }},
    {"other",{
      {"slice",{"bits(in0,in1)"}},
      {"concat",{"cat(in0,in1)"}},
      {"const",{"out <= value"}},
      {"term",{}},
      {"reg",{"reg myreg: UInt, clk, rst, init","myreg <= in","out <= myreg"}}, 
      //{"mem",""}, //TODO
    }}
  });
 
  
  std::map<std::string,std::vector<std::string>> coreInterfaceMap({
    {"unary",{
      "input in : UInt",
      "output out : UInt"
    }},
    {"unaryReduce",{
      "input in : UInt",
      "output out : UInt<1>"
    }},
    {"binary",{
      "input in0 : UInt",
      "input in1 : UInt",
      "output out : UInt"
    }},
    {"binaryReduce",{
      "input in0 : UInt",
      "input in1 : UInt",
      "output out : UInt<1>"
    }},
    {"const",{"input value : UInt","output out : UInt"}},
    {"term",{"input in : UInt"}},
    {"reg",{
      "input clk : Clock",
      "input rst : UInt<1>",
      "input in : UInt",
      "input init : UInt",
      "output out : UInt"
    }},
    {"mem",{
      "input clk : Clock",
      "input wdata : UInt",
      "input waddr : UInt",
      "input wen : UInt<1>",
      "output rdata : UInt",
      "input raddr : UInt"
    }}
  });

  Namespace* core = c->getNamespace("coreir");
  for (auto it0 : coreFMap) {
    for (auto it1 : it0.second) {
      string op = it1.first;
      auto fdef = it1.second;
      json fjson;
      fjson["prefix"] = "coreir_";
      fjson["definition"] = fdef;
      if (it0.first!="other") {
        fjson["interface"] = coreInterfaceMap[it0.first];
      }
      core->getGenerator(op)->getMetaData()["firrtl"] = fjson;
    }
  }

  //slice
  json fjson;
  fjson["prefix"] = "coreir_";
  fjson["definition"] = coreFMap["other"]["slice"];
  fjson["interface"] = coreInterfaceMap["unary"];
  core->getGenerator("slice")->getMetaData()["firrtl"] = fjson;
  
  //concat
  fjson["prefix"] = "coreir_";
  fjson["definition"] = coreFMap["other"]["concat"];
  fjson["interface"] = coreInterfaceMap["binary"];
  core->getGenerator("concat")->getMetaData()["firrtl"] = fjson;
   
  //const
  fjson["prefix"] = "coreir_";
  fjson["definition"] = coreFMap["other"]["const"];
  fjson["interface"] = coreInterfaceMap["const"];
  core->getGenerator("const")->getMetaData()["firrtl"] = fjson;
  
  //term
  fjson["prefix"] = "coreir_";
  fjson["definition"] = coreFMap["other"]["term"];
  fjson["interface"] = coreInterfaceMap["term"];
  core->getGenerator("const")->getMetaData()["firrtl"] = fjson;
  
  //reg
  fjson["prefix"] = "coreir_";
  fjson["definition"] = coreFMap["other"]["reg"];
  fjson["interface"] = coreInterfaceMap["reg"];
  core->getGenerator("const")->getMetaData()["firrtl"] = fjson;
  
}
