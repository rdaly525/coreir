

using namespace CoreIR;
using namespace std;
void CoreIRLoadFirrtl_corebit(Context* c) {
  std::map<std::string,std::map<std::string,std::vector<std::string>>> coreFMap({
    {"unary",{
      {"wire",{"out <= in"}},
      {"not",{"out <= not(in)"}},
    }},
    {"binary",{
      {"and",{"out <= and(in0,in1)"}},
      {"or",{"out <= or(in0,in1)"}},
      {"xor",{"out <= xor(in0,in1)"}},
    }},
    {"other",{
      {"mux",{"out <= mux(sel,in1,in0)"}}, //TODO is this the right ordering?
      {"concat",{"out <= cat(in0,in1)"}},
      {"const",{"out <= value"}},
      {"term",{""}},
      {"dff",{"reg myreg: UInt<1>, clk with:","  (reset =>(rst, init))","myreg <= in","out <= myreg"}}, 
      //{"mem",""}, //TODO
    }}
  });
 
  
//  std::map<std::string,std::vector<std::string>> coreInterfaceMap({
//    {"unary",{
//      "input in : UInt",
//      "output out : UInt"
//    }},
//    {"binary",{
//      "input in0 : UInt",
//      "input in1 : UInt",
//      "output out : UInt"
//    }},
//    {"mux",{
//      "input in0 : UInt",
//      "input in1 : UInt",
//      "input sel : UInt<1>",
//      "output out : UInt"
//    }},
//    {"const",{"input value : UInt","output out : UInt"}},
//    {"term",{"input in : UInt"}},
//    {"dff",{
//      "input clk : Clock",
//      "input rst : UInt<1>",
//      "input in : UInt",
//      "input init : UInt",
//      "output out : UInt"
//    }},
//  });

  Namespace* corebit = c->getNamespace("corebit");
  for (auto it0 : coreFMap) {
    for (auto it1 : it0.second) {
      string op = it1.first;
      auto fdef = it1.second;
      json fjson;
      fjson["prefix"] = "corebit_";
      fjson["definition"] = fdef;
      corebit->getModule(op)->getMetaData()["firrtl"] = fjson;
    }
  }

  //mux
  json fjson;
  fjson["prefix"] = "corebit_";
  fjson["definition"] = coreFMap["other"]["mux"];
  corebit->getModule("mux")->getMetaData()["firrtl"] = fjson;
  
  //const
  fjson["prefix"] = "corebit_";
  fjson["definition"] = coreFMap["other"]["const"];
  corebit->getModule("const")->getMetaData()["firrtl"] = fjson;
  
  //term
  
  //reg
  fjson["prefix"] = "corebit_";
  fjson["definition"] = coreFMap["other"]["dff"];
  corebit->getModule("dff")->getMetaData()["firrtl"] = fjson;
  
}
