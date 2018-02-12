#include "coreir.h"
#include "coreir/passes/analysis/smvmodule.hpp"
#include "coreir/passes/analysis/smvoperators.hpp"

#include <iostream>
using namespace CoreIR;
using namespace Passes;
using namespace std;

typedef void (*voidFunctionType)(void);

string SMVModule::toString() {
  ostringstream o;
  for (auto s : stmts) o << s << endl;
  return o.str();
}

string SMVModule::toVarDecString() {
  ostringstream o;
  for (auto vd : vardecs) o << vd << endl;
  return o.str();
}

string SMVModule::toNextVarDecString() {
  ostringstream o;
  for (auto vd : nextvardecs) o << vd << endl;
  return o.str();
}

string SMVModule::toInitVarDecString() {
  ostringstream o;
  for (auto vd : initvardecs) o << vd << endl;
  return o.str();
}

string SMVModule::toInstanceString(Instance* inst, string path) {
  string instname = inst->getInstname();
  Module* mref = inst->getModuleRef();
  ostringstream o;
  string tab = "  ";
  string mname;
  Values args;
  if (gen) {
    addPortsFromGen(inst);
    mname = modname; //gen->getNamespace()->getName() + "_" + gen->getName(args);
  }
  else {
    mname = modname;
  }

  // Even if not generator, there are some arguments in GenArgs and we want those too
  for (auto amap : mref->getGenArgs()) {
    ASSERT(args.count(amap.first)==0, "NYI Aliased config/genargs");
    args[amap.first] = amap.second;
  }

  for (auto amap : inst->getModArgs()) {
    ASSERT(args.count(amap.first)==0,"NYI Alisaaed config/genargs");
    args[amap.first] = amap.second;
  }
  vector<string> params;
  const json& jmeta = mref->getMetaData();
  
  if (jmeta.count("verilog") && jmeta["verilog"].count("parameters")) {
    params = jmeta["verilog"]["parameters"].get<vector<string>>();
  }
  else {
    for (auto amap : args) {
      params.push_back(amap.first);
    }
  }
  vector<string> paramstrs;
  for (auto param : params) {
    ASSERT(args.count(param),"Missing parameter " + param + " from " + ::CoreIR::toString(args));
    string astr = "." + param + "(" + args[param]->toString() + ")";
    paramstrs.push_back(astr);
  }
  //Assume names are <instname>_port
  unordered_map<string, SmvBVVar> portstrs;
  for (auto port : ports) {
    portstrs.emplace(port.getPortName(), port);
  }

  string context = path+"$";
  string pre = ""; //"coreir_";

  enum operation {neg_op = 1,
                  const_op,
                  add_op,
                  sub_op,
                  and_op,
                  or_op,
                  xor_op,
                  reg_op,
                  regPE_op,
                  concat_op,
                  slice_op,
                  term_op,
                  mux_op};

  unordered_map<string, operation> opmap;

  opmap.emplace(pre+"neg", neg_op);
  opmap.emplace(pre+"bitneg", neg_op);
  opmap.emplace(pre+"not", neg_op);
  opmap.emplace(pre+"bitnot", neg_op);
  opmap.emplace(pre+"const", const_op);
  opmap.emplace(pre+"bitconst", const_op);
  opmap.emplace(pre+"add", add_op);
  opmap.emplace(pre+"sub", sub_op);
  opmap.emplace(pre+"and", and_op);
  opmap.emplace(pre+"bitand", and_op);
  opmap.emplace(pre+"or", or_op);
  opmap.emplace(pre+"bitor", or_op);
  opmap.emplace(pre+"xor", xor_op);
  opmap.emplace(pre+"bitxor", xor_op);
  opmap.emplace(pre+"bitreg", reg_op);
  opmap.emplace(pre+"reg", reg_op);
  opmap.emplace(pre+"reg_PE", regPE_op);
  opmap.emplace(pre+"concat", concat_op);
  opmap.emplace(pre+"slice", slice_op);
  opmap.emplace(pre+"term", term_op);
  opmap.emplace(pre+"mux", mux_op);

#define var_assign(var, name) if (portstrs.find(name) != portstrs.end()) var = portstrs.find(name)->second
  
  SmvBVVar out; var_assign(out, "out");
  SmvBVVar in; var_assign(in, "in");
  SmvBVVar in0; var_assign(in0, "in0");
  SmvBVVar in1; var_assign(in1, "in1");
  SmvBVVar clk; var_assign(clk, "clk");
  SmvBVVar en; var_assign(en, "en");
  SmvBVVar sel; var_assign(sel, "sel");
  
  switch (opmap[mname]) {
  case term_op:
    break;
  case neg_op:
    o << SMVNot(context, in, out);
    break;
  case add_op:
    o << SMVAdd(context, in0, in1, out);
    break;
  case sub_op:
    o << SMVSub(context, in0, in1, out);
    break;
  case and_op:
    o << SMVAnd(context, in0, in1, out);
    break;
  case or_op:
    o << SMVOr(context, in0, in1, out);
    break;
  case xor_op:
    o << SMVXor(context, in0, in1, out);
    break;
  case concat_op:
    o << SMVConcat(context, in0, in1, out);
    break;
  case reg_op:
    o << SMVReg(context, in, clk, out);
    break;
  case regPE_op:
    o << SMVRegPE(context, in, clk, out, en);
    break;
  case const_op:
    int value; value = stoi(args["value"]->toString());
    o << SMVConst(context, out, value);
    break;
  case mux_op:
    o << SMVMux(context, in0, in1, sel, out);
    break;    
  case slice_op:
    int lo; lo = stoi(args["lo"]->toString());
    int hi; hi = stoi(args["hi"]->toString());
    o << SMVSlice(context, in, out, lo, hi-1);
    break;
  default:
    o << "!!! UNMATCHED: " << mname << " !!!";
  }
  
  o << endl;
  return o.str();
}

