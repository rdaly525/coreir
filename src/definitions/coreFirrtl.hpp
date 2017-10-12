

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
      {"ashr",{"out <= dshr(toSInt(in0),toSInt(in1))"}},
      {"add",{"out <= tail(add(in0,in1),1)"}},
      {"sub",{"out <= tail(sub(in0,in1),1)"}},
      {"mul",{"out <= mul(in0,in1)"}}, //TODO 
      {"udiv",{"out <= div(in0,in1)"}},
      {"sdiv",{"out <= div(toSInt(in0),toSInt(in1))"}},
    }},
    {"binaryReduce",{
      {"eq",{"out <= eq(in0,in1)"}},
      {"neq",{"out <= neq(in0,in1)"}},
      {"slt",{"out <= lt(asSInt(in0),asSInt(in1))"}},
      {"sgt",{"out <= gt(asSInt(in0),asSInt(in1))"}},
      {"sle",{"out <= leq(asSInt(in0),asSInt(in1))"}},
      {"sge",{"out <= geq(asSInt(in0),asSInt(in1))"}},
      {"ult",{"out <= lt(in0,in1)"}},
      {"ugt",{"out <= gt(in0,in1)"}},
      {"ule",{"out <= leq(in0,in1)"}},
      {"uge",{"out <= geq(in0,in1)"}},
    }},
    {"other",{
      {"mux",{"out <= mux(sel,in1,in0)"}}, //TODO is this the right ordering?
      {"slice",{"out <= dshr(in,lo)"}},
      {"concat",{"out <= cat(in0,in1)"}},
      {"const",{"out <= value"}},
      {"term",{""}},
      {"reg",{"reg myreg: UInt, clk","myreg <= in","out <= myreg"}}, 
      {"regrst",{"reg myreg: UInt, clk, rst, init","myreg <= in","out <= myreg"}}, 
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
    {"mux",{
      "input in0 : UInt",
      "input in1 : UInt",
      "input sel : UInt<1>",
      "output out : UInt"
    }},
    {"slice",{
      "input lo : UInt",
      "input in : UInt",
      "output out : UInt"
    }},
    {"const",{"input value : UInt","output out : UInt"}},
    {"term",{"input in : UInt"}},
    {"reg",{
      "input clk : Clock",
      "input in : UInt",
      "output out : UInt"
    }},
    {"regrst",{
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

  {
    //mux
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["mux"];
    fjson["interface"] = coreInterfaceMap["mux"];
    core->getGenerator("mux")->getMetaData()["firrtl"] = fjson;
  }
  {
    //slice
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["slice"];
    fjson["interface"] = coreInterfaceMap["slice"];
    fjson["parameters"] = {"lo"};
    core->getGenerator("slice")->getMetaData()["firrtl"] = fjson;
  }
  {
    //concat
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["concat"];
    fjson["interface"] = coreInterfaceMap["binary"];
    core->getGenerator("concat")->getMetaData()["firrtl"] = fjson;
  }
  {
    //const
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["const"];
    fjson["interface"] = coreInterfaceMap["const"];
    fjson["parameters"] = {"value"};
    core->getGenerator("const")->getMetaData()["firrtl"] = fjson;
  }
  {
    //term
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["term"];
    fjson["interface"] = coreInterfaceMap["term"];
    core->getGenerator("term")->getMetaData()["firrtl"] = fjson;
  }
  {
    //reg
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["reg"];
    fjson["interface"] = coreInterfaceMap["reg"];
    core->getGenerator("reg")->getMetaData()["firrtl"] = fjson;
  }
  {
    //regrst
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["regrst"];
    fjson["interface"] = coreInterfaceMap["regrst"];
    fjson["parameters"] = {"init"};
    core->getGenerator("regrst")->getMetaData()["firrtl"] = fjson;
  }
  //TODO Now do it for all the corebit
  //wire, not, and, or, xor, mux, const, term, 

}
