#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include "coreir-passes/analysis/smtoperators.hpp"

#include <iostream>
using namespace CoreIR;
using namespace Passes;

typedef void (*voidFunctionType)(void);

string SMTModule::toString() {
  ostringstream o;
  string tab = "  ";

  //Param declaraions
  for (auto p : params) {
    o << tab << "parameter " << p;
    if (paramDefaults.count(p)) {
      o << " = " << paramDefaults[p];
    }
    o << ";" << endl;
  }
  o << endl;
  
  for (auto s : stmts) o << s << endl;
  return o.str();
}

string SMTModule::toVarDecString() {
  ostringstream o;
  for (auto vd : vardecs) o << vd << endl;
  return o.str();
}

string SMTModule::toNextVarDecString() {
  ostringstream o;
  for (auto vd : nextvardecs) o << vd << endl;
  return o.str();
}

string SMTModule::toInitVarDecString() {
  ostringstream o;
  for (auto vd : initvardecs) o << vd << endl;
  return o.str();
}

string SMTModule::toInstanceString(Instance* inst, string path) {
  string instname = inst->getInstname();
  Instantiable* iref = inst->getInstantiableRef();
  if (this->gen) {
    ASSERT(inst->isGen(),"DEBUG ME:");
  }
  ostringstream o;
  string tab = "  ";
  string mname;
  Args args;
  if (gen) {
    args = inst->getGenArgs();
    addPortsFromGen(inst);
    mname = gen->getNamespace()->getName() + SEP + gen->getName(args);
  }
  else {
    mname = modname;
  }

  for (auto amap : inst->getConfigArgs()) {
    ASSERT(args.count(amap.first)==0,"NYI Alisaaed config/genargs");
    args[amap.first] = amap.second;
  }
  vector<string> params;
  const json& jmeta = iref->getMetaData();
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
    ASSERT(args.count(param),"Missing parameter " + param + " from " + Args2Str(args));
    string astr = "." + param + "(" + args[param]->toString() + ")";
    paramstrs.push_back(astr);
  }
  //Assume names are <instname>_port
  unordered_map<string, SmtBVVar> portstrs;
  for (auto port : ports) {
    portstrs.emplace(port.getPortName(), port);
  }

  string context = path+SEP;
  string pre = "coreir"+SEP;

  enum operation {neg_op = 1,
                  const_op,
                  add_op,
                  and_op,
                  or_op,
                  reg_op,
                  regPE_op,
                  concat_op,
                  slice_op,
                  term_op};

  unordered_map<string, operation> opmap;

  opmap.emplace(pre+"neg", neg_op);
  opmap.emplace(pre+"const", const_op);
  opmap.emplace(pre+"add", add_op);
  opmap.emplace(pre+"and", and_op);
  opmap.emplace(pre+"or", or_op);
  opmap.emplace(pre+"reg", reg_op);
  opmap.emplace(pre+"reg_PE", regPE_op);
  opmap.emplace(pre+"concat", concat_op);
  opmap.emplace(pre+"slice", slice_op);
  opmap.emplace(pre+"term", term_op);

#define var_assign(var, name) if (portstrs.find(name) != portstrs.end()) var = portstrs.find(name)->second
  
  SmtBVVar out; var_assign(out, "out");
  SmtBVVar in; var_assign(in, "in");
  SmtBVVar in0; var_assign(in0, "in0");
  SmtBVVar in1; var_assign(in1, "in1");
  SmtBVVar clk; var_assign(clk, "clk");
  SmtBVVar en; var_assign(en, "en");
  
  switch (opmap[mname]) {
  case term_op:
    break;
  case neg_op:
    o << SMTNot(context, in, out);
    break;
  case add_op:
    o << SMTAdd(context, in0, in1, out);
    break;
  case and_op:
    o << SMTAnd(context, in0, in1, out);
    break;
  case or_op:
    o << SMTOr(context, in0, in1, out);
    break;
  case concat_op:
    o << SMTConcat(context, in0, in1, out);
    break;
  case regPE_op:
    o << SMTRegPE(context, in, clk, out, en);
    break;
  case const_op:
    int width; width = stoi(args["width"]->toString());
    int value; value = stoi(args["value"]->toString());
    o << SMTConst(context, out, getSMTbits(width, value));
    break;
  case slice_op:
    int lo; lo = stoi(args["lo"]->toString());
    int hi; hi = stoi(args["hi"]->toString());
    o << SMTSlice(context, in, out, lo, hi-1);
    break;
  default:
    o << "!!! UNMATCHED: " << mname << " !!!";
  }
  
  o << endl;
  return o.str();
}
