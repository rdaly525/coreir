#include "coreir/libs/cgralib.h"

COREIR_GEN_C_API_DEFINITION_FOR_LIBRARY(cgralib);

using namespace std;
using namespace CoreIR;

Namespace* CoreIRLoadLibrary_cgralib(Context* c) {
  
  Namespace* cgralib = c->newNamespace("cgralib");
  
  
  //PE declaration
  Params PEGenParams = {{"op_kind",c->String()},{"width",c->Int()},{"numbitports",c->Int()},{"numdataports",c->Int()}};
  
  cgralib->newTypeGen("PEType",PEGenParams,[](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
    uint numdataports = args.at("numdataports")->get<int>();
    uint numbitports = args.at("numbitports")->get<int>();
    return c->Record({
      {"data",c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(numdataports)},
        {"out",c->Bit()->Arr(width)}
      })},
      {"bit",c->Record({
        {"in",c->BitIn()->Arr(numbitports)},
        {"out",c->Bit()}
      })}
    });
  });
 
  //Generates the mod params and the default mod args
  auto PEModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params p; //params
    Values d; //defaults
    string op_kind = genargs.at("op_kind")->get<string>();
    int numbitports = genargs.at("numbitports")->get<int>();
    int numdataports = genargs.at("numdataports")->get<int>();
    int width = genargs.at("width")->get<int>();
    if (op_kind == "data" || op_kind == "combined") {
      p["alu_op"] = c->String();
      for (int i=0; i<numdataports; ++i) {
        string mode = "data"+to_string(i)+"_mode";
        p[mode] = c->String();
        d[mode] = Const::make(c,"BYPASS");
        string value = "data"+to_string(i)+"_value";
        p[value] = c->BitVector(width);
        d[value] = Const::make(c,BitVector(width,0));
      }
    }
    if (op_kind == "bit" || op_kind == "combined") {
      p["lut_value"] = c->BitVector(1<<numbitports);
      d["lut_value"] = Const::make(c,BitVector(1<<numbitports,0));
      cout << "LUTVAL=" << d["lut_value"]->toString() << endl;
      for (int i=0; i<numbitports; ++i) {
        string mode = "bit"+to_string(i)+"_mode";
        p[mode] = c->String();
        d[mode] = Const::make(c,"BYPASS");
        string value = "bit"+to_string(i)+"_value";
        p[value] = c->Bool();
        d[value] = Const::make(c,false);
      }
    }
    return {p,d};
  };
 
//Will produce something like this for combined
//    {"alu_op",c->String()}, //add,sub,shl,etc
//    {"lut_value",c->BitVector(8)}, //LUT for the optype=Bit (or combined)
//    {"data0_mode",c->String()},//TODO
//    {"data0_value",c->Int()}, //Value for constant
//    {"data1_mode",c->String()},
//    {"data1_value",c->Int()},
//    {"bit0_mode",c->String()},
//    {"bit0_value",c->Bool()},
  
  
  Generator* PE = cgralib->newGeneratorDecl("PE",cgralib->getTypeGen("PEType"),PEGenParams);
  PE->addDefaultGenArgs({{"width",Const::make(c,16)},{"numdataports",Const::make(c,2)},{"numbitports",Const::make(c,3)}});
  PE->setModParamsGen(PEModParamFun);

  //Unary op declaration
  Params widthParams = {{"width",c->Int()}};
  cgralib->newTypeGen("unary",widthParams,[](Context* c, Values args) { 
    uint width = args.at("width")->get<int>();
    return c->Record({
      {"in",c->BitIn()->Arr(width)},
      {"out",c->Bit()->Arr(width)},
    });
  });

  //IO Declaration
  Params modeParams = {{"mode",c->String()}};
  Generator* IO = cgralib->newGeneratorDecl("IO",cgralib->getTypeGen("unary"),widthParams);
  IO->setModParamsGen(modeParams);
  cgralib->newModuleDecl("BitIO",c->Record({{"in",c->BitIn()},{"out",c->Bit()}}),modeParams);
  
  //Mem declaration
  Params MemGenParams = {{"width",c->Int()},{"depth",c->Int()}};
  Params MemModParams = {
    {"mode",c->String()},
    {"fifo_depth",c->Int()},
    {"almost_full_cnt",c->Int()}
  };
  cgralib->newTypeGen("MemType",MemGenParams,[](Context* c, Values args) {
    uint width = args.at("width")->get<int>();
    return c->Record({
      {"waddr", c->BitIn()->Arr(width)},
      {"wdata", c->BitIn()->Arr(width)},
      {"wen", c->BitIn()},
      {"raddr", c->BitIn()->Arr(width)},
      {"rdata", c->Bit()->Arr(width)},
      {"ren", c->BitIn()},
      {"almost_full", c->Bit()},
      {"valid", c->Bit()}
    });
  });
  auto MemModParamFun = [](Context* c,Values genargs) -> std::pair<Params,Values> {
    Params p; //params
    Values d; //defaults
    p["mode"] = c->String();
    p["fifo_depth"] = c->Int();
    d["fifo_depth"] = Const::make(c,1024);
    p["almost_full_cnt"] = c->Int();
    d["almost_full_cnt"] = Const::make(c,0);
    return {p,d};
  };

  Generator* Mem = cgralib->newGeneratorDecl("Mem",cgralib->getTypeGen("MemType"),MemGenParams);
  Mem->addDefaultGenArgs({{"width",Const::make(c,16)},{"depth",Const::make(c,1024)}});
  Mem->setModParamsGen(MemModParamFun);

  return cgralib;
}


COREIR_GEN_EXTERNAL_API_FOR_LIBRARY(cgralib)
