using namespace CoreIR;
using namespace std;

// The coreir namespace is for multi-bit primitives.
// TODO: deduplicate overlapping code with corebitFirrtl.hpp

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
      {"mux",{"out <= mux(sel, in1, in0)"}},
      {"slice",{"out <= bits(in,%hi%,%lo%)"}},
      {"concat",{"out <= cat(in1, in0)"}}, // TODO: implement this properly
      {"const",{"out <= value"}},
      {"term",{""}},
      {"tribuf", {"out is invalid"}}, // TODO: implement this
      {"ibuf", {"in is invalid", "out is invalid"}}, // TODO: implement this
      {"pullresistor", {"out is invalid"}}, // TODO: implement this
      {"reg", {
        "node regClock = asClock(mux(clk_posedge, asUInt(clk), not(asUInt(clk))))",
        "wire resetWire : UInt<1>",
        "resetWire <= UInt<1>(\"h00\")",
        "reg myreg : UInt, regClock with : (reset => (resetWire, init))",
        "myreg <= in",
        "out <= myreg"
      }},
      {"reg_arst", {"out is invalid"}}, // firrtl primitive registers don't support async reset yet
      //{"mem",""}, //TODO
    }}
  });
 
  /*
  std::map<std::string,std::vector<std::string>> coreInterfaceMap({
    {"unary",{
      "input in : UInt<%width%>",
      "output out : UInt<%width%>"
    }},
    {"unaryReduce",{
      "input in : UInt<%width%>",
      "output out : UInt<1>"
    }},
    {"binary",{
      "input in0 : UInt<%width%>",
      "input in1 : UInt<%width%>",
      "output out : UInt<%width%>"
    }},
    {"binaryReduce",{
      "input in0 : UInt<%width%>",
      "input in1 : UInt<%width%>",
      "output out : UInt<1>"
    }},
    {"mux",{
      "input in0 : UInt<%width%>",
      "input in1 : UInt<%width%>",
      "input sel : UInt<1>",
      "output out : UInt<%width%>"
    }},
    {"slice",{
      "input in : UInt<%width%>",
      "output out : UInt<%hi%-%lo%>"
    }},
    {"const",{
      "input value : UInt<%width%>",
      "output out : UInt<%width%>"
    }},
    {"term",{"input in : UInt<%width%>"}},
    {"reg",{
      "input clk : Clock",
      "input in : UInt<%width%>",
      "output out : UInt<%width%>"
      "input init : UInt<%width%>",
    }},
    {"regrst",{
      "input clk : Clock",
      "input rst : UInt<1>",
      "input in : UInt<%width%>",
      "input init : UInt<%width%>",
      "output out : UInt<%width%>"
    }},
//    {"mem",{
//      "input clk : Clock",
//      "input wdata : UInt",
//      "input waddr : UInt",
//      "input wen : UInt<1>",
//      "output rdata : UInt",
//      "input raddr : UInt"
//    }}
  });
*/
  Namespace* core = c->getNamespace("coreir");
  for (auto it0 : coreFMap) {
    for (auto it1 : it0.second) {
      string op = it1.first;
      auto fdef = it1.second;
      json fjson;
      fjson["parameters"] = {"width"};
      fjson["prefix"] = "coreir_";
      fjson["definition"] = fdef;
      //if (it0.first!="other") {
      //  fjson["interface"] = coreInterfaceMap[it0.first];
      //}
      core->getGenerator(op)->getMetaData()["firrtl"] = fjson;
    }
  }

  {
    //mux
    json fjson;
    fjson["parameters"] = {"width"};
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["mux"];
    //fjson["interface"] = coreInterfaceMap["mux"];
    core->getGenerator("mux")->getMetaData()["firrtl"] = fjson;
  }
  {
    //slice
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["slice"];
    //fjson["interface"] = coreInterfaceMap["slice"];
    fjson["parameters"] = {"width","lo","hi"};
    core->getGenerator("slice")->getMetaData()["firrtl"] = fjson;
  }
  {
    //concat
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["concat"];
    //fjson["interface"] = coreInterfaceMap["binary"];
    fjson["parameters"] = {"width0","width1"};
    core->getGenerator("concat")->getMetaData()["firrtl"] = fjson;
  }
  {
    //const
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["const"];
    //fjson["interface"] = coreInterfaceMap["const"];
    fjson["parameters"] = {"width"};
    core->getGenerator("const")->getMetaData()["firrtl"] = fjson;
  }
  {
    //term
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["term"];
    //fjson["interface"] = coreInterfaceMap["term"];
    fjson["parameters"] = {"width"};
    core->getGenerator("term")->getMetaData()["firrtl"] = fjson;
  }
  {
    //reg
    json fjson;
    fjson["prefix"] = "coreir_";
    fjson["definition"] = coreFMap["other"]["reg"];
    //fjson["interface"] = coreInterfaceMap["reg"];
    fjson["parameters"] = {"width"};
    core->getGenerator("reg")->getMetaData()["firrtl"] = fjson;
  }
  //TODO Now do it for all the corebit
  //wire, not, and, or, xor, mux, const, term, 

}
